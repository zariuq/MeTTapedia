import Mettapedia.GSLT.LanguageDef.NativeOpsControlCorrespondence
import Mettapedia.GSLT.LanguageDef.NativeOpsLoweringBoundaries

/-!
# Continuations of the existing label-resolving target

These laws relocate finite TargetRun derivations to a larger enclosing block.
They retain each instruction's actual state effects. A normal prefix runs its
continuation once; a return or outward jump skips it. Label freshness belongs
to the compilation supply, independently of the execution relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Label)

mutual
  def CodeJumpsRespect (accept : Label → Prop) : List Instruction → Prop
    | [] => True
    | first :: rest => InstructionJumpsRespect accept first ∧ CodeJumpsRespect accept rest
  termination_by code => sizeOf code
  decreasing_by all_goals simp_wf; all_goals omega

  def InstructionJumpsRespect (accept : Label → Prop) : Instruction → Prop
    | .jump label => accept label
    | .scope body | .forWord _ _ body => CodeJumpsRespect accept body
    | .branch _ yes no => CodeJumpsRespect accept yes ∧ CodeJumpsRespect accept no
    | .switch _ arms otherwise => ArmJumpsRespect accept arms ∧ CodeJumpsRespect accept otherwise
    | _ => True
  termination_by instruction => sizeOf instruction
  decreasing_by all_goals simp_wf; all_goals omega

  def ArmJumpsRespect (accept : Label → Prop) : List (BitVec 64 × List Instruction) → Prop
    | [] => True
    | (_, body) :: rest => CodeJumpsRespect accept body ∧ ArmJumpsRespect accept rest
  termination_by arms => sizeOf arms
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Numeric bounds are one observation of the common jump-target predicate. -/
def CodeJumpsWithin (bound : Nat) (code : List Instruction) : Prop :=
  CodeJumpsRespect (fun label => label.identity ≤ bound) code

def InstructionJumpsWithin (bound : Nat) (instruction : Instruction) : Prop :=
  InstructionJumpsRespect (fun label => label.identity ≤ bound) instruction

def ArmJumpsWithin (bound : Nat) (arms : List (BitVec 64 × List Instruction)) : Prop :=
  ArmJumpsRespect (fun label => label.identity ≤ bound) arms

/-- Only labels visible to the current root are constrained. Nested roots
    are checked separately, as in TargetInstructionEval. -/
def TopLabelsAbove (bound : Nat) (code : List Instruction) : Prop :=
  ∀ label, Instruction.label label ∈ code → bound < label.identity

def TopLabelsAtMost (bound : Nat) (code : List Instruction) : Prop :=
  ∀ label, Instruction.label label ∈ code → label.identity ≤ bound

theorem top_labels_at_most_append (bound : Nat) (first second : List Instruction) :
    TopLabelsAtMost bound (first ++ second) ↔
      TopLabelsAtMost bound first ∧ TopLabelsAtMost bound second := by
  constructor
  · intro all
    exact ⟨fun label member => all label (List.mem_append_left second member),
      fun label member => all label (List.mem_append_right first member)⟩
  · rintro ⟨left, right⟩ label member
    rcases List.mem_append.mp member with earlier | later
    · exact left label earlier
    · exact right label later

theorem top_labels_at_most_weaken {lower upper : Nat} (inside : lower ≤ upper)
    {code : List Instruction} (bounded : TopLabelsAtMost lower code) : TopLabelsAtMost upper code :=
  fun label member => (bounded label member).trans inside

theorem top_labels_at_most_singleton (bound : Nat) (instruction : Instruction)
    (notLabel : ∀ label, Instruction.label label ≠ instruction) :
    TopLabelsAtMost bound [instruction] := by
  intro label member
  exact False.elim (notLabel label (List.mem_singleton.mp member))

theorem top_labels_at_most_of_label_free {code : List Instruction}
    (checked : TopLabelFree code) (bound : Nat) : TopLabelsAtMost bound code := by
  intro label member
  exact False.elim (checked label member)

theorem code_jumps_respect_append (accept : Label → Prop) (first second : List Instruction) :
    CodeJumpsRespect accept (first ++ second) ↔
      CodeJumpsRespect accept first ∧ CodeJumpsRespect accept second := by
  induction first with
  | nil => simp only [List.nil_append, CodeJumpsRespect, true_and]
  | cons head tail ih =>
      simp only [List.cons_append, CodeJumpsRespect, ih, and_assoc]

theorem arm_jumps_respect_cons (accept : Label → Prop) (arm : BitVec 64 × List Instruction)
    (rest : List (BitVec 64 × List Instruction)) :
    ArmJumpsRespect accept (arm :: rest) ↔
      CodeJumpsRespect accept arm.2 ∧ ArmJumpsRespect accept rest := by
  cases arm
  simp only [ArmJumpsRespect]

theorem code_jumps_within_append (bound : Nat) (first second : List Instruction) :
    CodeJumpsWithin bound (first ++ second) ↔
      CodeJumpsWithin bound first ∧ CodeJumpsWithin bound second :=
  code_jumps_respect_append (fun label => label.identity ≤ bound) first second

theorem arm_jumps_within_cons (bound : Nat) (arm : BitVec 64 × List Instruction)
    (rest : List (BitVec 64 × List Instruction)) :
    ArmJumpsWithin bound (arm :: rest) ↔
      CodeJumpsWithin bound arm.2 ∧ ArmJumpsWithin bound rest :=
  arm_jumps_respect_cons (fun label => label.identity ≤ bound) arm rest

theorem jump_free_arms_cons (arm : BitVec 64 × List Instruction)
    (rest : List (BitVec 64 × List Instruction)) :
    jumpFreeArms (arm :: rest) = (jumpFreeCode arm.2 && jumpFreeArms rest) := by
  cases arm
  simp only [jumpFreeArms]

mutual
  theorem code_jumps_respect_mono {lower upper : Label → Prop} (inside : ∀ label, lower label → upper label)
      {code : List Instruction} (bounded : CodeJumpsRespect lower code) : CodeJumpsRespect upper code := by
    cases code with
    | nil => simp only [CodeJumpsRespect]
    | cons first rest =>
        simp only [CodeJumpsRespect] at bounded ⊢
        exact ⟨instruction_jumps_respect_mono inside bounded.1,
          code_jumps_respect_mono inside bounded.2⟩
  termination_by sizeOf code
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem instruction_jumps_respect_mono {lower upper : Label → Prop} (inside : ∀ label, lower label → upper label)
      {instruction : Instruction} (bounded : InstructionJumpsRespect lower instruction) :
      InstructionJumpsRespect upper instruction := by
    cases instruction <;> simp only [InstructionJumpsRespect] at bounded ⊢
    all_goals first
      | exact inside _ bounded
      | exact code_jumps_respect_mono inside bounded
      | exact ⟨code_jumps_respect_mono inside bounded.1, code_jumps_respect_mono inside bounded.2⟩
      | exact ⟨arm_jumps_respect_mono inside bounded.1, code_jumps_respect_mono inside bounded.2⟩
  termination_by sizeOf instruction
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem arm_jumps_respect_mono {lower upper : Label → Prop} (inside : ∀ label, lower label → upper label)
      {arms : List (BitVec 64 × List Instruction)} (bounded : ArmJumpsRespect lower arms) :
      ArmJumpsRespect upper arms := by
    cases arms with
    | nil => simp only [ArmJumpsRespect]
    | cons arm rest =>
        rw [arm_jumps_respect_cons] at bounded ⊢
        exact ⟨code_jumps_respect_mono inside bounded.1, arm_jumps_respect_mono inside bounded.2⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals first | omega | (cases arm; simp_all; omega)
end

mutual
  theorem code_jumps_respect_of_all {accept : Label → Prop} (every : ∀ label, accept label)
      (code : List Instruction) : CodeJumpsRespect accept code := by
    cases code with
    | nil => simp only [CodeJumpsRespect]
    | cons head tail =>
        simp only [CodeJumpsRespect]
        exact ⟨instruction_jumps_respect_of_all every head, code_jumps_respect_of_all every tail⟩
  termination_by sizeOf code
  decreasing_by all_goals simp_wf; all_goals omega

  theorem instruction_jumps_respect_of_all {accept : Label → Prop} (every : ∀ label, accept label)
      (instruction : Instruction) : InstructionJumpsRespect accept instruction := by
    cases instruction <;> simp only [InstructionJumpsRespect]
    all_goals first
      | exact every _
      | exact code_jumps_respect_of_all every _
      | exact ⟨code_jumps_respect_of_all every _, code_jumps_respect_of_all every _⟩
      | exact ⟨arm_jumps_respect_of_all every _, code_jumps_respect_of_all every _⟩
  termination_by sizeOf instruction
  decreasing_by all_goals simp_wf; all_goals omega

  theorem arm_jumps_respect_of_all {accept : Label → Prop} (every : ∀ label, accept label)
      (arms : List (BitVec 64 × List Instruction)) : ArmJumpsRespect accept arms := by
    cases arms with
    | nil => simp only [ArmJumpsRespect]
    | cons arm rest =>
        rw [arm_jumps_respect_cons]
        exact ⟨code_jumps_respect_of_all every arm.2, arm_jumps_respect_of_all every rest⟩
  termination_by sizeOf arms
  decreasing_by all_goals simp_wf; all_goals first | omega | (cases arm; simp_all; omega)
end

theorem code_jumps_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
    {code : List Instruction} (bounded : CodeJumpsWithin lower code) : CodeJumpsWithin upper code :=
  code_jumps_respect_mono (fun _ earlier => earlier.trans inside) bounded

theorem instruction_jumps_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
    {instruction : Instruction} (bounded : InstructionJumpsWithin lower instruction) :
    InstructionJumpsWithin upper instruction :=
  instruction_jumps_respect_mono (fun _ earlier => earlier.trans inside) bounded

theorem arm_jumps_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
    {arms : List (BitVec 64 × List Instruction)} (bounded : ArmJumpsWithin lower arms) :
    ArmJumpsWithin upper arms :=
  arm_jumps_respect_mono (fun _ earlier => earlier.trans inside) bounded

mutual
  theorem jump_free_code_respects (accept : Label → Prop) {code : List Instruction}
      (checked : jumpFreeCode code = true) : CodeJumpsRespect accept code := by
    cases code with
    | nil => simp only [CodeJumpsRespect]
    | cons first rest =>
        simp only [jumpFreeCode, Bool.and_eq_true] at checked
        simp only [CodeJumpsRespect]
        exact ⟨jump_free_instruction_respects accept checked.1, jump_free_code_respects accept checked.2⟩
  termination_by sizeOf code
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem jump_free_instruction_respects (accept : Label → Prop) {instruction : Instruction}
      (checked : jumpFreeInstruction instruction = true) : InstructionJumpsRespect accept instruction := by
    cases instruction <;> simp only [jumpFreeInstruction, InstructionJumpsRespect,
      Bool.and_eq_true, Bool.false_eq_true] at checked ⊢
    all_goals first
      | exact jump_free_code_respects accept checked
      | exact ⟨jump_free_code_respects accept checked.1, jump_free_code_respects accept checked.2⟩
      | exact ⟨jump_free_arms_respects accept checked.1, jump_free_code_respects accept checked.2⟩
  termination_by sizeOf instruction
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem jump_free_arms_respects (accept : Label → Prop) {arms : List (BitVec 64 × List Instruction)}
      (checked : jumpFreeArms arms = true) : ArmJumpsRespect accept arms := by
    cases arms with
    | nil => simp only [ArmJumpsRespect]
    | cons arm rest =>
        rw [jump_free_arms_cons, Bool.and_eq_true] at checked
        rw [arm_jumps_respect_cons]
        exact ⟨jump_free_code_respects accept checked.1, jump_free_arms_respects accept checked.2⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals first | omega | (cases arm; simp_all; omega)
end

theorem jump_free_code_within (bound : Nat) {code : List Instruction}
    (checked : jumpFreeCode code = true) : CodeJumpsWithin bound code :=
  jump_free_code_respects (fun label => label.identity ≤ bound) checked

theorem jump_free_instruction_within (bound : Nat) {instruction : Instruction}
    (checked : jumpFreeInstruction instruction = true) : InstructionJumpsWithin bound instruction :=
  jump_free_instruction_respects (fun label => label.identity ≤ bound) checked

theorem jump_free_arms_within (bound : Nat) {arms : List (BitVec 64 × List Instruction)}
    (checked : jumpFreeArms arms = true) : ArmJumpsWithin bound arms :=
  jump_free_arms_respects (fun label => label.identity ≤ bound) checked

theorem after_label_suffix_respects {accept : Label → Prop} {code suffix : List Instruction} {label : Label}
    (accepted : CodeJumpsRespect accept code) (found : targetAfterLabel? code label = some suffix) :
    CodeJumpsRespect accept suffix := by
  induction code with
  | nil => cases found
  | cons head tail ih =>
      simp only [CodeJumpsRespect] at accepted
      have tailBound := accepted.2
      cases head <;> simp only [targetAfterLabel?] at found
      all_goals first
        | exact ih tailBound found
        | split at found
          · cases Option.some.inj found
            exact tailBound
          · exact ih tailBound found

theorem after_label_suffix_within {bound : Nat} {code suffix : List Instruction} {label : Label}
    (bounded : CodeJumpsWithin bound code) (found : targetAfterLabel? code label = some suffix) :
    CodeJumpsWithin bound suffix := after_label_suffix_respects bounded found

theorem top_labels_above_append (bound : Nat) (first second : List Instruction) :
    TopLabelsAbove bound (first ++ second) ↔
      TopLabelsAbove bound first ∧ TopLabelsAbove bound second := by
  constructor
  · intro fresh
    exact ⟨fun label member => fresh label (List.mem_append_left _ member),
      fun label member => fresh label (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ label member
    rcases List.mem_append.mp member with old | later
    · exact left label old
    · exact right label later

theorem top_labels_above_weaken {lower upper : Nat} (inside : lower ≤ upper)
    {code : List Instruction} (fresh : TopLabelsAbove upper code) : TopLabelsAbove lower code :=
  fun label member => inside.trans_lt (fresh label member)

theorem top_labels_above_singleton (bound : Nat) (instruction : Instruction)
    (notLabel : ∀ label, Instruction.label label ≠ instruction) : TopLabelsAbove bound [instruction] := by
  intro label member
  exact False.elim (notLabel label (List.mem_singleton.mp member))

theorem pure_temporary_top_labels_above (bound : Nat) (supply : NativeIR.Supply)
    (type : NativeType) (operation : NativeIR.PureOperation) :
    TopLabelsAbove bound (NativeLowering.pureTemporary supply type operation).code :=
  top_labels_above_singleton bound _ (fun _ impossible => by cases impossible)

theorem guarded_top_labels_above {interface : Interface} {scope : Scope} {expression : Expr}
    (supported : SourceGuardedExpression expression) {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) (bound : Nat) :
    TopLabelsAbove bound output.code := by
  intro label member
  have fresh := (guarded_lowering_bounds supported compiled).2.1 (.label label) member
  rcases fresh with ⟨_, _, _, impossible, _, _⟩ | ⟨_, _, impossible⟩
  · cases impossible
  · cases impossible

theorem short_circuit_top_labels_above {interface : Interface} {scope : Scope} {expression : Expr}
    (supported : SourceShortCircuitExpression expression) {supply : NativeIR.Supply}
    {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) (bound : Nat) :
    TopLabelsAbove bound output.code := by
  induction supported generalizing supply output with
  | guarded child => exact guarded_top_labels_above child compiled bound
  | connect continueValue first second firstIH secondIH =>
      obtain ⟨left, right, _, _, leftCompiled, _, same⟩ := short_circuit_lowering_exact continueValue compiled
      subst output
      apply (top_labels_above_append bound _ _).mpr
      refine ⟨(top_labels_above_append bound _ _).mpr ⟨firstIH leftCompiled,
        pure_temporary_top_labels_above bound _ _ _⟩, ?_⟩
      exact top_labels_above_singleton bound _ (fun _ impossible => by cases impossible)

theorem after_label_none_of_above {bound : Nat} {code : List Instruction} {label : Label}
    (fresh : TopLabelsAbove bound code) (earlier : label.identity ≤ bound) :
    targetAfterLabel? code label = none := by
  induction code with
  | nil => rfl
  | cons head tail ih =>
      have tailFresh : TopLabelsAbove bound tail :=
        fun candidate member => fresh candidate (List.mem_cons_of_mem _ member)
      cases head <;> simp only [targetAfterLabel?]
      all_goals first
        | exact ih tailFresh
        | rename_i candidate
          have different : candidate ≠ label := by
            intro same
            subst candidate
            exact Nat.not_lt_of_ge earlier (fresh label (List.mem_cons_self))
          exact (if_neg different).trans (ih tailFresh)

theorem after_label_append (first second : List Instruction) (label : Label) :
    targetAfterLabel? (first ++ second) label =
      match targetAfterLabel? first label with
      | some suffix => some (suffix ++ second)
      | none => targetAfterLabel? second label := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      cases head <;> simp only [List.cons_append, targetAfterLabel?]
      all_goals first
        | exact ih
        | split
          · rfl
          · exact ih

theorem after_label_none_of_at_most {bound : Nat} {code : List Instruction} {label : Label}
    (bounded : TopLabelsAtMost bound code) (newer : bound < label.identity) :
    targetAfterLabel? code label = none := by
  induction code with
  | nil => rfl
  | cons head tail ih =>
      have tailBound : TopLabelsAtMost bound tail :=
        fun candidate member => bounded candidate (List.mem_cons_of_mem head member)
      cases head <;> simp only [targetAfterLabel?]
      all_goals first
        | exact ih tailBound
        | rename_i candidate
          have different : ¬ candidate = label := by
            intro same
            subst candidate
            exact (Nat.not_le_of_gt newer) (bounded label List.mem_cons_self)
          exact (if_neg different).trans (ih tailBound)

theorem fresh_continuation_lookup {bound : Nat} (root continuation : List Instruction)
    (fresh : TopLabelsAbove bound continuation) (label : Label) (earlier : label.identity ≤ bound) :
    targetAfterLabel? (root ++ continuation) label =
      (targetAfterLabel? root label).map (fun suffix => suffix ++ continuation) := by
  rw [after_label_append]
  cases targetAfterLabel? root label with
  | none => exact after_label_none_of_above fresh earlier
  | some suffix => rfl

theorem selected_case_respects {accept : Label → Prop} (value : BitVec 64)
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
    (armBound : ArmJumpsRespect accept arms) (otherwiseBound : CodeJumpsRespect accept otherwise) :
    CodeJumpsRespect accept (targetSelectCase value arms otherwise) := by
  induction arms with
  | nil => simpa only [targetSelectCase, List.find?_nil] using otherwiseBound
  | cons arm rest ih =>
      rcases arm with ⟨selector, body⟩
      simp only [ArmJumpsRespect] at armBound
      by_cases same : selector == value
      · simpa [targetSelectCase, same] using armBound.1
      · simpa [targetSelectCase, same] using ih armBound.2

theorem within_selected_case {bound : Nat} (value : BitVec 64)
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
    (armBound : ArmJumpsWithin bound arms) (otherwiseBound : CodeJumpsWithin bound otherwise) :
    CodeJumpsWithin bound (targetSelectCase value arms otherwise) :=
  selected_case_respects value armBound otherwiseBound

local macro "respect_execution_cases" : tactic => `(tactic| (
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
    simp only [InstructionJumpsRespect] at checked
    exact ih label checked jumped
  case branch =>
    rename_i tested selected ih label checked jumped
    simp only [InstructionJumpsRespect] at checked
    apply ih label ?_ ?_ jumped
    all_goals split <;> first | exact checked.1 | exact checked.2
  case switch =>
    rename_i value selected ih label checked jumped
    simp only [InstructionJumpsRespect] at checked
    apply ih label ?_ ?_ jumped
    all_goals exact selected_case_respects _ checked.1 checked.2
  case scope =>
    rename_i ran ih label checked jumped
    simp only [InstructionJumpsRespect] at checked
    exact ih label checked checked jumped
  case label => rename_i label checked jumped; cases jumped
  case jump =>
    rename_i label checked jumped
    simp only [InstructionJumpsRespect] at checked
    cases jumped
    exact checked
  case «return» => rename_i label checked jumped; cases jumped
  case nil => rename_i label rootBound checked jumped; cases jumped
  case next =>
    rename_i first rest ihFirst ihRest label rootBound checked jumped
    simp only [CodeJumpsRespect] at checked
    exact ihRest label rootBound checked.2 jumped
  case «return» => rename_i label rootBound checked jumped; cases jumped
  case resume =>
    rename_i first found rest ihFirst ihRest label rootBound checked jumped
    exact ihRest label rootBound (after_label_suffix_respects rootBound found) jumped
  case escape =>
    rename_i first outside ih label rootBound checked jumped
    simp only [CodeJumpsRespect] at checked
    exact ih label checked.1 jumped
  case done => rename_i label checked jumped; cases jumped
  case next =>
    rename_i readCounter readBound within ran normal counterAfter rest ihRun ihRest label checked jumped
    exact ihRest label checked jumped
  case stop =>
    rename_i readCounter readBound within ran abrupt ih label checked jumped
    exact ih label checked checked jumped))

theorem instruction_jump_respects {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {accept : Label → Prop}
    (ran : TargetInstructionEval interface heap calls result instruction frame state out) :
    ∀ label, InstructionJumpsRespect accept instruction → out.flow = .jumped label → accept label := by
  induction ran using TargetInstructionEval.rec
    (motive_2 := fun root code _ _ out _ =>
      ∀ label, CodeJumpsRespect accept root → CodeJumpsRespect accept code →
        out.flow = .jumped label → accept label)
    (motive_3 := fun _ _ body _ _ out _ =>
      ∀ label, CodeJumpsRespect accept body → out.flow = .jumped label → accept label)
  respect_execution_cases

theorem run_jump_respects {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {accept : Label → Prop}
    (ran : TargetRun interface heap calls result root code frame state out) :
    ∀ label, CodeJumpsRespect accept root → CodeJumpsRespect accept code →
      out.flow = .jumped label → accept label := by
  induction ran using TargetRun.rec
    (motive_1 := fun instruction _ _ out _ =>
      ∀ label, InstructionJumpsRespect accept instruction → out.flow = .jumped label → accept label)
    (motive_3 := fun _ _ body _ _ out _ =>
      ∀ label, CodeJumpsRespect accept body → out.flow = .jumped label → accept label)
  respect_execution_cases

theorem instruction_jump_within {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {bound : Nat}
    (ran : TargetInstructionEval interface heap calls result instruction frame state out) :
    ∀ label, InstructionJumpsWithin bound instruction → out.flow = .jumped label → label.identity ≤ bound :=
  instruction_jump_respects ran

theorem run_jump_within {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {bound : Nat}
    (ran : TargetRun interface heap calls result root code frame state out) :
    ∀ label, CodeJumpsWithin bound root → CodeJumpsWithin bound code →
      out.flow = .jumped label → label.identity ≤ bound := run_jump_respects ran

/-- Continuation behavior uses TargetRun itself, including its label root. -/
inductive TargetContinues {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (root continuation : List Instruction) : TargetBlockOutcome World → TargetBlockOutcome World → Prop
  | normal {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
      (ran : TargetRun interface heap calls result root continuation frame state out) :
      TargetContinues interface heap calls result root continuation ⟨.normal, frame, state⟩ out
  | returned (value : TargetValue) (frame : TargetFrame) (state : TargetState World) :
      TargetContinues interface heap calls result root continuation
        ⟨.returned value, frame, state⟩ ⟨.returned value, frame, state⟩
  | jumped (label : Label) (frame : TargetFrame) (state : TargetState World) :
      TargetContinues interface heap calls result root continuation
        ⟨.jumped label, frame, state⟩ ⟨.jumped label, frame, state⟩

/- The instruction and initialization subtrees are deliberately inert in this
   induction principle: relocation reuses their original derivations verbatim.
   Only the existing finite TargetRun spine changes its enclosing label root. -/
private theorem target_run_spine_induction {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (P : List Instruction → List Instruction → TargetFrame → TargetState World → TargetBlockOutcome World → Prop)
    (nilCase : ∀ root frame state, P root [] frame state ⟨.normal, frame, state⟩)
    (nextCase : ∀ {root rest first before middle pre post out},
      TargetInstructionEval interface heap calls result first before pre ⟨.normal, middle, post⟩ →
      TargetRun interface heap calls result root rest middle post out → P root rest middle post out →
      P root (first :: rest) before pre out)
    (returnCase : ∀ {root rest first value before after pre post},
      TargetInstructionEval interface heap calls result first before pre ⟨.returned value, after, post⟩ →
      P root (first :: rest) before pre ⟨.returned value, after, post⟩)
    (resumeCase : ∀ {root rest suffix first label before middle pre post out},
      TargetInstructionEval interface heap calls result first before pre ⟨.jumped label, middle, post⟩ →
      targetAfterLabel? root label = some suffix →
      TargetRun interface heap calls result root suffix middle post out → P root suffix middle post out →
      P root (first :: rest) before pre out)
    (escapeCase : ∀ {root rest first label before after pre post},
      TargetInstructionEval interface heap calls result first before pre ⟨.jumped label, after, post⟩ →
      targetAfterLabel? root label = none →
      P root (first :: rest) before pre ⟨.jumped label, after, post⟩)
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} (ran : TargetRun interface heap calls result root code frame state out) :
    P root code frame state out := by
  induction ran using TargetRun.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
  all_goals repeat intro
  all_goals first | exact True.intro | skip
  case nil => exact nilCase _ _ _
  case next =>
    rename_i firstRun restRun unused tailIH
    exact nextCase firstRun restRun tailIH
  case «return» =>
    rename_i firstRun unused
    exact returnCase firstRun
  case resume =>
    rename_i firstRun found restRun unused tailIH
    exact resumeCase firstRun found restRun tailIH
  case escape =>
    rename_i firstRun outside unused
    exact escapeCase firstRun outside

theorem target_extend_continuation {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code continuation : List Instruction} {bound : Nat}
    (rootBound : CodeJumpsWithin bound root) (codeBound : CodeJumpsWithin bound code)
    (fresh : TopLabelsAbove bound continuation)
    {frame : TargetFrame} {state : TargetState World} {prefixOut out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root code frame state prefixOut)
    (following : TargetContinues interface heap calls result (root ++ continuation) continuation prefixOut out) :
    TargetRun interface heap calls result (root ++ continuation) (code ++ continuation) frame state out := by
  let P := fun root code frame state prefixOut =>
    ∀ {continuation : List Instruction} {bound : Nat},
      CodeJumpsWithin bound root → CodeJumpsWithin bound code → TopLabelsAbove bound continuation →
      ∀ {out : TargetBlockOutcome World},
        TargetContinues interface heap calls result (root ++ continuation) continuation prefixOut out →
        TargetRun interface heap calls result (root ++ continuation) (code ++ continuation) frame state out
  have allRuns : P root code frame state prefixOut := by
    refine target_run_spine_induction (P := P) ?_ ?_ ?_ ?_ ?_ ran
    · intro root frame state continuation bound rootBound codeBound fresh out following
      cases following with
      | normal continued => exact continued
    · intro root rest first before middle pre post final firstRun restRun ih continuation bound
        rootBound codeBound fresh out following
      simp only [CodeJumpsWithin, CodeJumpsRespect] at codeBound
      exact .next firstRun (ih rootBound codeBound.2 fresh following)
    · intro root rest first value before after pre post firstRun continuation bound rootBound codeBound
        fresh out following
      cases following
      exact .return firstRun
    · intro root rest suffix first label before middle pre post final firstRun found restRun ih continuation
        bound rootBound codeBound fresh out following
      simp only [CodeJumpsWithin, CodeJumpsRespect] at codeBound
      have within := instruction_jump_within firstRun label codeBound.1 rfl
      have extended := fresh_continuation_lookup root continuation fresh label within
      rw [found, Option.map_some] at extended
      exact .resume firstRun extended (ih rootBound (after_label_suffix_within rootBound found) fresh following)
    · intro root rest first label before after pre post firstRun outside continuation bound rootBound codeBound
        fresh out following
      simp only [CodeJumpsWithin, CodeJumpsRespect] at codeBound
      have within := instruction_jump_within firstRun label codeBound.1 rfl
      have extended := fresh_continuation_lookup root continuation fresh label within
      rw [outside, Option.map_none] at extended
      cases following
      exact .escape firstRun extended
  exact allRuns rootBound codeBound fresh following

theorem target_split_continuation {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code continuation : List Instruction} {bound : Nat}
    (rootBound : CodeJumpsWithin bound root) (codeBound : CodeJumpsWithin bound code)
    (fresh : TopLabelsAbove bound continuation)
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result (root ++ continuation) (code ++ continuation) frame state out) :
    ∃ prefixOut, TargetRun interface heap calls result root code frame state prefixOut ∧
      TargetContinues interface heap calls result (root ++ continuation) continuation prefixOut out := by
  let P := fun fullRoot program frame state out =>
    ∀ {root code continuation : List Instruction} {bound : Nat},
      CodeJumpsWithin bound root → CodeJumpsWithin bound code → TopLabelsAbove bound continuation →
      fullRoot = root ++ continuation → program = code ++ continuation →
      ∃ prefixOut, TargetRun interface heap calls result root code frame state prefixOut ∧
        TargetContinues interface heap calls result fullRoot continuation prefixOut out
  have allRuns : P (root ++ continuation) (code ++ continuation) frame state out := by
    refine target_run_spine_induction (P := P) ?_ ?_ ?_ ?_ ?_ ran
    · intro fullRoot frame state root code continuation bound rootBound codeBound fresh sameRoot sameCode
      cases code with
      | nil =>
          cases sameCode
          exact ⟨⟨.normal, frame, state⟩, .nil root frame state, .normal (.nil fullRoot frame state)⟩
      | cons first rest => cases sameCode
    · intro fullRoot rest first before middle pre post final firstRun restRun ih root code continuation bound
        rootBound codeBound fresh sameRoot sameCode
      subst fullRoot
      cases code with
      | nil =>
          cases sameCode
          exact ⟨⟨.normal, before, pre⟩, .nil root before pre, .normal (.next firstRun restRun)⟩
      | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at sameCode
          rcases sameCode with ⟨sameFirst, sameRest⟩
          cases sameFirst
          simp only [CodeJumpsWithin, CodeJumpsRespect] at codeBound
          obtain ⟨prefixOut, prefixRan, following⟩ := ih rootBound codeBound.2 fresh rfl sameRest
          exact ⟨prefixOut, .next firstRun prefixRan, following⟩
    · intro fullRoot rest first value before after pre post firstRun root code continuation bound rootBound
        codeBound fresh sameRoot sameCode
      subst fullRoot
      cases code with
      | nil =>
          cases sameCode
          exact ⟨⟨.normal, before, pre⟩, .nil root before pre, .normal (.return firstRun)⟩
      | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at sameCode
          rcases sameCode with ⟨sameFirst, _⟩
          cases sameFirst
          exact ⟨_, .return firstRun, .returned _ _ _⟩
    · intro fullRoot rest suffix first label before middle pre post final firstRun found restRun ih root code
        continuation bound rootBound codeBound fresh sameRoot sameCode
      subst fullRoot
      cases code with
      | nil =>
          cases sameCode
          exact ⟨⟨.normal, before, pre⟩, .nil root before pre, .normal (.resume firstRun found restRun)⟩
      | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at sameCode
          rcases sameCode with ⟨sameFirst, _⟩
          cases sameFirst
          simp only [CodeJumpsWithin, CodeJumpsRespect] at codeBound
          have within := instruction_jump_within firstRun label codeBound.1 rfl
          have extended := fresh_continuation_lookup root continuation fresh label within
          obtain ⟨oldSuffix, originalFound, sameSuffix⟩ := Option.map_eq_some_iff.mp (extended.symm.trans found)
          obtain ⟨prefixOut, prefixRan, following⟩ :=
            ih rootBound (after_label_suffix_within rootBound originalFound) fresh rfl sameSuffix.symm
          exact ⟨prefixOut, .resume firstRun originalFound prefixRan, following⟩
    · intro fullRoot rest first label before after pre post firstRun outside root code continuation bound rootBound
        codeBound fresh sameRoot sameCode
      subst fullRoot
      cases code with
      | nil =>
          cases sameCode
          exact ⟨⟨.normal, before, pre⟩, .nil root before pre, .normal (.escape firstRun outside)⟩
      | cons head tail =>
          simp only [List.cons_append, List.cons.injEq] at sameCode
          rcases sameCode with ⟨sameFirst, _⟩
          cases sameFirst
          simp only [CodeJumpsWithin, CodeJumpsRespect] at codeBound
          have within := instruction_jump_within firstRun label codeBound.1 rfl
          have extended := fresh_continuation_lookup root continuation fresh label within
          have originalOutside := Option.map_eq_none_iff.mp (extended.symm.trans outside)
          exact ⟨_, .escape firstRun originalOutside, .jumped _ _ _⟩
  exact allRuns rootBound codeBound fresh rfl rfl

theorem target_continuation_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code continuation : List Instruction} {bound : Nat}
    (rootBound : CodeJumpsWithin bound root) (codeBound : CodeJumpsWithin bound code)
    (fresh : TopLabelsAbove bound continuation)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (root ++ continuation) (code ++ continuation) frame state out ↔
      ∃ prefixOut, TargetRun interface heap calls result root code frame state prefixOut ∧
        TargetContinues interface heap calls result (root ++ continuation) continuation prefixOut out := by
  constructor
  · exact target_split_continuation rootBound codeBound fresh
  · rintro ⟨prefixOut, ran, following⟩
    exact target_extend_continuation rootBound codeBound fresh ran following

theorem top_labels_above_nil (bound : Nat) : TopLabelsAbove bound [] := by
  intro label member
  cases member

theorem target_single_nonlabel_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (instruction : Instruction) (notLabel : ∀ label, Instruction.label label ≠ instruction)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result [instruction] [instruction] frame state out ↔
      TargetInstructionEval interface heap calls result instruction frame state out := by
  have outside : ∀ label, targetAfterLabel? [instruction] label = none := by
    intro label
    exact after_label_none_of_above (top_labels_above_singleton label.identity instruction notLabel)
      (Nat.le_refl _)
  constructor
  · intro ran
    cases ran with
    | next first rest => cases rest; exact first
    | «return» first => exact first
    | resume first found rest => rw [outside] at found; cases found
    | escape first absent => exact first
  · intro first
    rcases out with ⟨flow, after, post⟩
    cases flow with
    | normal => exact .next first (.nil [instruction] after post)
    | returned value => exact .return first
    | jumped label => exact .escape first (outside label)

theorem target_scope_body_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (body : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result [.scope body] [.scope body] frame state out ↔
      ∃ inner, TargetRun interface heap calls result body body frame state inner ∧
        out = targetCloseBlock frame inner := by
  rw [target_single_nonlabel_exact _ (fun _ impossible => by cases impossible)]
  constructor
  · intro ran
    cases ran with
    | scope inner => exact ⟨_, inner, rfl⟩
  · rintro ⟨inner, ran, same⟩
    subst out
    exact .scope ran

theorem target_branch_body_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {condition : NativeIR.Condition} {yes no : List Instruction} {selected : Bool}
    {frame : TargetFrame} {state : TargetState World}
    (tested : TargetConditionEval interface frame state condition selected) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result [.branch condition yes no] [.branch condition yes no] frame state out ↔
      ∃ inner, TargetRun interface heap calls result
          (if selected then yes else no) (if selected then yes else no) frame state inner ∧
        out = targetCloseBlock frame inner := by
  rw [target_single_nonlabel_exact _ (fun _ impossible => by cases impossible)]
  exact target_branch_instruction_exact tested out

theorem target_close_self {World : Type} (frame : TargetFrame) (state : TargetState World)
    (hscope : TemporariesScoped frame) (flow : TargetFlow) :
    targetCloseBlock frame ⟨flow, frame, state⟩ = ⟨flow, frame, state⟩ := by
  unfold targetCloseBlock
  rw [targetLeaveScope_self frame state hscope]

/-- One iteration of the emitted label/scope loop is an actual body run.
The entry restarts from the cleaned frame, the exit finishes normally, and
other jumps remain outward transfers. Label lookup retains its first-match
order even when a malformed caller supplies equal entry and exit labels. -/
theorem target_scoped_loop_iteration_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (entry exit : Label) (body : List Instruction) (frame : TargetFrame)
    (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result [.label entry, .scope body, .label exit]
      [.label entry, .scope body, .label exit] frame state out ↔
      ∃ inner, TargetRun interface heap calls result body body frame state inner ∧
        match inner.flow with
        | .normal | .returned _ => out = targetCloseBlock frame inner
        | .jumped label =>
            if entry = label then
              TargetRun interface heap calls result [.label entry, .scope body, .label exit]
                [.scope body, .label exit] (targetCloseBlock frame inner).frame
                (targetCloseBlock frame inner).state out
            else if exit = label then
              out = ⟨.normal, (targetCloseBlock frame inner).frame, (targetCloseBlock frame inner).state⟩
            else out = targetCloseBlock frame inner := by
  rw [target_label_cons_exact, target_scope_cons_exact]
  apply exists_congr
  rintro ⟨flow, after, post⟩
  apply and_congr_right
  intro bodyRan
  cases flow with
  | normal =>
      rw [target_label_cons_exact, target_run_empty_exact]
      rfl
  | returned value => rfl
  | jumped label =>
      by_cases entered : entry = label
      · simp only [targetAfterLabel?, entered, if_true]
      · by_cases exited : exit = label
        · simp only [targetAfterLabel?, entered, exited, if_false, if_true]
          rw [target_run_empty_exact]
        · simp only [targetAfterLabel?, entered, exited, if_false]

/-- Only lookups admitted by the actual code need agree. Nested instruction
    roots and complete outcomes are reused from the supplied execution. -/
theorem target_run_relocate_root_lookups {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {accept : Label → Prop}
    (ran : TargetRun interface heap calls result root code frame state out)
    (destination : List Instruction)
    (reachable : ∀ label, accept label → ∀ suffix,
      targetAfterLabel? root label = some suffix → CodeJumpsRespect accept suffix)
    (codeReads : CodeJumpsRespect accept code)
    (lookups : ∀ label, accept label →
      targetAfterLabel? destination label = targetAfterLabel? root label) :
    TargetRun interface heap calls result destination code frame state out := by
  let P := fun root code frame state out =>
    ∀ destination,
      (∀ label, accept label → ∀ suffix,
        targetAfterLabel? root label = some suffix → CodeJumpsRespect accept suffix) →
      CodeJumpsRespect accept code →
      (∀ label, accept label → targetAfterLabel? destination label = targetAfterLabel? root label) →
      TargetRun interface heap calls result destination code frame state out
  have relocated : P root code frame state out := by
    refine target_run_spine_induction (P := P) ?_ ?_ ?_ ?_ ?_ ran
    · intro root frame state destination reachable codeReads lookups
      exact .nil destination frame state
    · intro root rest first before middle pre post out head tail ih destination reachable codeReads lookups
      simp only [CodeJumpsRespect] at codeReads
      exact .next head (ih destination reachable codeReads.2 lookups)
    · intro root rest first value before after pre post head destination reachable codeReads lookups
      exact .return head
    · intro root rest suffix first label before middle pre post out head found tail ih destination
        reachable codeReads lookups
      simp only [CodeJumpsRespect] at codeReads
      have accepted := instruction_jump_respects head label codeReads.1 rfl
      exact .resume head ((lookups label accepted).trans found)
        (ih destination reachable (reachable label accepted suffix found) lookups)
    · intro root rest first label before after pre post head outside destination reachable codeReads lookups
      simp only [CodeJumpsRespect] at codeReads
      have accepted := instruction_jump_respects head label codeReads.1 rfl
      exact .escape head ((lookups label accepted).trans outside)
  exact relocated destination reachable codeReads lookups

/-- A root whose whole code respects the predicate supplies the reachable
    suffix condition without any additional assumption. -/
theorem target_run_relocate_root_on {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {accept : Label → Prop}
    (ran : TargetRun interface heap calls result root code frame state out)
    (destination : List Instruction)
    (rootReads : CodeJumpsRespect accept root) (codeReads : CodeJumpsRespect accept code)
    (lookups : ∀ label, accept label →
      targetAfterLabel? destination label = targetAfterLabel? root label) :
    TargetRun interface heap calls result destination code frame state out :=
  target_run_relocate_root_lookups ran destination
    (fun _ _ _ found => after_label_suffix_respects rootReads found) codeReads lookups

/-- Equality of the reachable label lookups supports both directions. The
    second root may contain unrelated earlier code which is never entered. -/
theorem target_run_root_lookup_on_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {accept : Label → Prop}
    (destination : List Instruction)
    (rootReads : CodeJumpsRespect accept root) (codeReads : CodeJumpsRespect accept code)
    (lookups : ∀ label, accept label →
      targetAfterLabel? destination label = targetAfterLabel? root label)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root code frame state out ↔
      TargetRun interface heap calls result destination code frame state out := by
  constructor
  · intro ran
    exact target_run_relocate_root_on ran destination rootReads codeReads lookups
  · intro ran
    apply target_run_relocate_root_lookups ran root ?_ codeReads
      (fun label accepted => (lookups label accepted).symm)
    intro label accepted suffix found
    exact after_label_suffix_respects rootReads ((lookups label accepted).symm.trans found)

/-- Changing only an enclosing root with identical label lookups preserves
    each finite execution, including nested instruction effects. -/
theorem target_run_relocate_root {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root code frame state out)
    (destination : List Instruction)
    (lookups : ∀ label, targetAfterLabel? destination label = targetAfterLabel? root label) :
    TargetRun interface heap calls result destination code frame state out :=
  target_run_relocate_root_on ran destination
    (code_jumps_respect_of_all lookups root) (code_jumps_respect_of_all lookups code)
    (fun _ agreed => agreed)

/-- A prefix without labels queried by this run cannot intercept its jumps. -/
theorem target_run_prefix_root_on {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {accept : Label → Prop}
    (ran : TargetRun interface heap calls result root code frame state out)
    (earlier : List Instruction)
    (rootReads : CodeJumpsRespect accept root) (codeReads : CodeJumpsRespect accept code)
    (absent : ∀ label, accept label → targetAfterLabel? earlier label = none) :
    TargetRun interface heap calls result (earlier ++ root) code frame state out := by
  apply target_run_relocate_root_on ran (earlier ++ root) rootReads codeReads
  intro label accepted
  rw [after_label_append, absent label accepted]

/-- Removing an earlier prefix is as sound as adding it when its visible
    labels cannot answer any lookup admitted by the executed fragment. -/
theorem target_run_prefix_root_on_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {accept : Label → Prop}
    (earlier : List Instruction)
    (rootReads : CodeJumpsRespect accept root) (codeReads : CodeJumpsRespect accept code)
    (absent : ∀ label, accept label → targetAfterLabel? earlier label = none)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root code frame state out ↔
      TargetRun interface heap calls result (earlier ++ root) code frame state out := by
  apply target_run_root_lookup_on_iff (earlier ++ root) rootReads codeReads
  intro label accepted
  rw [after_label_append, absent label accepted]

theorem target_run_root_lookup_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (first second code : List Instruction)
    (lookups : ∀ label, targetAfterLabel? first label = targetAfterLabel? second label)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result first code frame state out ↔
      TargetRun interface heap calls result second code frame state out := by
  exact ⟨fun ran => target_run_relocate_root ran second (fun label => (lookups label).symm),
    fun ran => target_run_relocate_root ran first lookups⟩

/-- The real while guard either transfers to the exit or continues unchanged.
The branch's lexical close is discharged by the supplied scoped frame. -/
theorem target_loop_guard_instruction_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {condition : NativeIR.Atom} {selected : Bool} {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state condition (.bool selected))
    (hscope : TemporariesScoped frame) (exit : Label) (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result
      (.branch (.negated condition) [.jump exit] []) frame state out ↔
      out = ⟨if selected then .normal else .jumped exit, frame, state⟩ := by
  rw [target_branch_instruction_exact (TargetConditionEval.negated read)]
  cases selected with
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, ite_true]
      constructor
      · rintro ⟨inner, ran, closed⟩
        cases (target_run_empty_exact [] frame state inner).mp ran
        simpa only [target_close_self frame state hscope] using closed
      · intro same
        exact ⟨_, .nil [] frame state,
          by simpa only [target_close_self frame state hscope] using same⟩
  | false =>
      simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
      constructor
      · rintro ⟨inner, ran, closed⟩
        have jumped := (target_single_nonlabel_exact (.jump exit)
          (fun _ impossible => by cases impossible) frame state inner).mp ran
        cases jumped with
        | jump => simpa only [target_close_self frame state hscope] using closed
      · intro same
        exact ⟨_, .escape (.jump exit frame state) rfl,
          by simpa only [target_close_self frame state hscope] using same⟩

theorem expression_jumps_within {interface : Interface} {scope : Scope} {expression : Expr}
    {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output) (bound : Nat) :
    CodeJumpsWithin bound output.code :=
  jump_free_code_within bound (expression_lowering_jump_free interface scope expression supply output compiled)

theorem location_jumps_within {interface : Interface} {scope : Scope} {location : Expr}
    {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.location? interface scope location supply = some output) (bound : Nat) :
    CodeJumpsWithin bound output.code :=
  jump_free_code_within bound (location_lowering_jump_free interface scope location supply output compiled)

theorem label_free_above {code : List Instruction} (checked : TopLabelFree code) (bound : Nat) :
    TopLabelsAbove bound code := fun label member => False.elim (checked label member)

theorem label_free_prefix_lookup {earlier : List Instruction} (checked : TopLabelFree earlier)
    (body : List Instruction) (label : Label) :
    targetAfterLabel? (earlier ++ body) label = targetAfterLabel? body label := by
  rw [after_label_append,
    after_label_none_of_above (label_free_above checked label.identity) (Nat.le_refl _)]

/-- The separately evaluated condition prefix cannot capture any loop-body
jump when its actual code contains no top-level label. -/
theorem target_label_free_prefix_root_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {earlier : List Instruction} (checked : TopLabelFree earlier)
    (body code : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (earlier ++ body) code frame state out ↔
      TargetRun interface heap calls result body code frame state out :=
  target_run_root_lookup_iff _ _ _ (label_free_prefix_lookup checked body) frame state out

theorem fresh_loop_labels_within (supply : NativeIR.Supply) {loops : List NativeIR.LoopLabels}
    (bounded : LoopLabelsWithin supply.next loops) :
    LoopLabelsWithin (NativeIR.fresh (NativeIR.fresh supply).2).2.next
      (freshLoopLabels supply :: loops) := by
  intro active member
  rcases List.mem_cons.mp member with same | old
  · subst active
    simp only [freshLoopLabels, NativeIR.fresh]
    exact ⟨Nat.le_succ _, Nat.le_refl _⟩
  · exact (loop_labels_within_weaken
      (Nat.le_of_lt ((NativeIR.fresh_strict supply).trans
        (NativeIR.fresh_strict (NativeIR.fresh supply).2))) bounded) active old

mutual
  /-- All jumps are old loop exits/entries or identifiers actually allocated
      by this statement. Visible labels are strictly newer than its input. -/
  theorem statement_lowering_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {statement : Statement}
      {supply : NativeIR.Supply}
      {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.statement? interface result loops scope statement supply = some output) :
      supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
        TopLabelsAbove supply.next output.code := by
    cases statement with
    | declare name type initializer =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := declaration_lowering_exact compiled
        subst output
        refine ⟨(expression_lowering_boundary _ _ _ _ _ lowered).monotone, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨label_free_above (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | set location child =>
        obtain ⟨nextScope, place, value, _, located, lowered, same⟩ := set_lowering_exact compiled
        have locationBound := location_lowering_boundary _ _ _ _ _ located
        have valueBound := expression_lowering_boundary _ _ _ _ _ lowered
        subst output
        refine ⟨locationBound.monotone.trans valueBound.monotone, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨(code_jumps_within_append _ _ _).mpr
              ⟨location_jumps_within located _, expression_jumps_within lowered _⟩,
              by simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr
            ⟨(top_labels_above_append _ _ _).mpr
              ⟨label_free_above locationBound.labelFree _, label_free_above valueBound.labelFree _⟩,
              top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | branch condition yes no =>
        obtain ⟨nextScope, test, whenTrue, whenFalse, _, testCompiled, yesCompiled, noCompiled, same⟩ :=
          branch_lowering_exact compiled
        have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
        have yesBounds := block_lowering_bounds (loop_labels_within_weaken testBound bounded) yesCompiled
        have noBounds := block_lowering_bounds
          (loop_labels_within_weaken yesBounds.1 (loop_labels_within_weaken testBound bounded)) noCompiled
        subst output
        refine ⟨testBound.trans (yesBounds.1.trans noBounds.1), ?_, ?_⟩
        · apply (code_jumps_within_append _ _ _).mpr
          refine ⟨expression_jumps_within testCompiled _, ?_⟩
          simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]
          exact ⟨⟨code_jumps_within_weaken noBounds.1 yesBounds.2.1, noBounds.2.1⟩, True.intro⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨label_free_above (expression_lowering_boundary _ _ _ _ _ testCompiled).labelFree _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | «while» condition body =>
        obtain ⟨nextScope, test, iteration, _, testCompiled, bodyCompiled, same⟩ := while_lowering_exact compiled
        have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
        have bodyBounds := block_lowering_bounds
          (loop_labels_within_weaken testBound (fresh_loop_labels_within supply bounded)) bodyCompiled
        have exitBound : (freshLoopLabels supply).exit.identity ≤ iteration.supply.next :=
          testBound.trans bodyBounds.1
        have entryBound : (freshLoopLabels supply).entry.identity ≤ iteration.supply.next :=
          (fresh_loop_labels_above_supply supply).2.le.trans exitBound
        subst output
        refine ⟨?_, ?_, ?_⟩
        · exact (NativeIR.fresh_strict supply).le.trans
            ((NativeIR.fresh_strict (NativeIR.fresh supply).2).le.trans (testBound.trans bodyBounds.1))
        · simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]
          refine ⟨True.intro, ?_, True.intro, True.intro⟩
          apply (code_jumps_within_append _ _ _).mpr
          refine ⟨(code_jumps_within_append _ _ _).mpr ⟨?_, bodyBounds.2.1⟩, ?_⟩
          · apply (code_jumps_within_append _ _ _).mpr
            refine ⟨expression_jumps_within testCompiled _, ?_⟩
            simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]
            exact ⟨⟨⟨exitBound, True.intro⟩, True.intro⟩, True.intro⟩
          · simpa only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect] using And.intro entryBound True.intro
        · intro label member
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
          rcases member with entry | impossible | exit
          · cases Instruction.label.inj entry
            exact (fresh_loop_labels_above_supply supply).1
          · cases impossible
          · cases Instruction.label.inj exit
            exact (fresh_loop_labels_above_supply supply).1.trans (fresh_loop_labels_above_supply supply).2
    | switch selector arms otherwise =>
        rw [NativeLowering.statement?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨selected, selectorCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨armOutput, armsCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨defaultOutput, otherwiseCompiled, compiled⟩
        have selectorBound := expression_lowering_boundary _ _ _ _ _ selectorCompiled
        have armBounds := cases_lowering_bounds (loop_labels_within_weaken selectorBound.monotone bounded) armsCompiled
        have defaultBounds := block_lowering_bounds
          (loop_labels_within_weaken armBounds.1 (loop_labels_within_weaken selectorBound.monotone bounded))
          otherwiseCompiled
        cases Option.some.inj compiled
        refine ⟨selectorBound.monotone.trans (armBounds.1.trans defaultBounds.1), ?_, ?_⟩
        · apply (code_jumps_within_append _ _ _).mpr
          refine ⟨expression_jumps_within selectorCompiled _, ?_⟩
          simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]
          exact ⟨⟨arm_jumps_within_weaken defaultBounds.1 armBounds.2, defaultBounds.2.1⟩, True.intro⟩
        · exact (top_labels_above_append _ _ _).mpr
            ⟨label_free_above selectorBound.labelFree _,
              top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | free child =>
        rw [NativeLowering.statement?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨value, lowered, compiled⟩
        have valueBound := expression_lowering_boundary _ _ _ _ _ lowered
        cases type with
        | ref element | array element =>
            cases Option.some.inj compiled
            refine ⟨valueBound.monotone, ?_, ?_⟩
            · exact (code_jumps_within_append _ _ _).mpr
                ⟨expression_jumps_within lowered _,
                  by simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
            · exact (top_labels_above_append _ _ _).mpr
                ⟨label_free_above valueBound.labelFree _, by
                  intro label member
                  simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member⟩
        | _ => cases compiled
    | «break» =>
        obtain ⟨active, outer, same, outputSame⟩ := break_lowering_exact compiled
        subst loops
        subst output
        refine ⟨Nat.le_refl _, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect] using
          And.intro (bounded active (List.mem_cons_self)).2 True.intro
    | «continue» =>
        obtain ⟨active, outer, same, outputSame⟩ := continue_lowering_exact compiled
        subst loops
        subst output
        refine ⟨Nat.le_refl _, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect] using
          And.intro (bounded active (List.mem_cons_self)).1 True.intro
    | effect child =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := effect_lowering_exact compiled
        subst output
        exact ⟨(expression_lowering_boundary _ _ _ _ _ lowered).monotone, expression_jumps_within lowered _,
          label_free_above (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _⟩
    | «return» value =>
        cases value with
        | none =>
            obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
            subst output
            exact ⟨Nat.le_refl _, by simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]; trivial,
              top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        | some child =>
            obtain ⟨nextScope, value, _, lowered, same⟩ := return_value_lowering_exact compiled
            subst output
            refine ⟨(expression_lowering_boundary _ _ _ _ _ lowered).monotone, ?_, ?_⟩
            · exact (code_jumps_within_append _ _ _).mpr
                ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
            · exact (top_labels_above_append _ _ _).mpr ⟨label_free_above (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
                top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | block child =>
        obtain ⟨nextScope, body, _, lowered, same⟩ := block_statement_lowering_exact compiled
        have bodyBounds := block_lowering_bounds bounded lowered
        subst output
        refine ⟨bodyBounds.1, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, CodeJumpsRespect, InstructionJumpsRespect] using And.intro bodyBounds.2.1 True.intro
  termination_by sizeOf statement
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem block_lowering_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {body : List Statement}
      {supply : NativeIR.Supply}
      {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.block? interface result loops scope body supply = some output) :
      supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
        TopLabelsAbove supply.next output.code := by
    cases body with
    | nil =>
        rw [NativeLowering.block?] at compiled
        cases Option.some.inj compiled
        exact ⟨Nat.le_refl _, by simp only [CodeJumpsWithin, CodeJumpsRespect], top_labels_above_nil _⟩
    | cons head tail =>
        obtain ⟨first, rest, firstCompiled, restCompiled, same⟩ := block_cons_lowering_exact compiled
        have firstBounds := statement_lowering_bounds bounded firstCompiled
        have restBounds := block_lowering_bounds
          (loop_labels_within_weaken firstBounds.1 bounded) restCompiled
        subst output
        exact ⟨firstBounds.1.trans restBounds.1,
          (code_jumps_within_append _ _ _).mpr
            ⟨code_jumps_within_weaken restBounds.1 firstBounds.2.1, restBounds.2.1⟩,
          (top_labels_above_append _ _ _).mpr
            ⟨firstBounds.2.2, top_labels_above_weaken firstBounds.1 restBounds.2.2⟩⟩
  termination_by sizeOf body
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem cases_lowering_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope}
      {arms : List (NativeWord64.Word × List Statement)} {supply : NativeIR.Supply}
      {output : NativeLowering.Cases} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.cases? interface result loops scope arms supply = some output) :
      supply.next ≤ output.supply.next ∧ ArmJumpsWithin output.supply.next output.cases := by
    cases arms with
    | nil =>
        rw [NativeLowering.cases?] at compiled
        cases Option.some.inj compiled
        exact ⟨Nat.le_refl _, by simp only [ArmJumpsWithin, ArmJumpsRespect]⟩
    | cons arm rest =>
        cases arm with
        | mk selector body =>
            rw [NativeLowering.cases?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨bodyOutput, bodyCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨restOutput, restCompiled, compiled⟩
            have bodyBounds := block_lowering_bounds bounded bodyCompiled
            have restBounds := cases_lowering_bounds (loop_labels_within_weaken bodyBounds.1 bounded) restCompiled
            cases Option.some.inj compiled
            exact ⟨bodyBounds.1.trans restBounds.1,
              (arm_jumps_within_cons _ _ _).mpr
                ⟨code_jumps_within_weaken restBounds.1 bodyBounds.2.1, restBounds.2⟩⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end


theorem local_control_statement_bounds {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {statement : Statement}
    (_supported : SourceLocalControlStatement statement) {supply : NativeIR.Supply}
    {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface result loops scope statement supply = some output) :
    supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
      TopLabelsAbove supply.next output.code := statement_lowering_bounds bounded compiled

theorem local_control_block_bounds {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {body : List Statement}
    (_supported : SourceLocalControlBlock body) {supply : NativeIR.Supply}
    {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.block? interface result loops scope body supply = some output) :
    supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
      TopLabelsAbove supply.next output.code := block_lowering_bounds bounded compiled

/-- A jump outside the active root retains the complete caller frame and
state. The absence premise is about the actual root lookup. -/
theorem target_outward_jump_run_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root : List Instruction) (label : Label) (outside : targetAfterLabel? root label = none)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.jump label] frame state out ↔
      out = ⟨.jumped label, frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | next first rest => cases first
    | «return» first => cases first
    | resume first found rest => cases first; rw [outside] at found; cases found
    | escape first absent => cases first; rfl
  · intro same
    subst out
    exact .escape (.jump label frame state) outside

/-- Appending the emitted back edge changes only normal completion into an
entry transfer. Existing returns and outward transfers skip the back edge.
Its entry is absent from the actual body root. -/
def targetLoopBackedge {World : Type} (entry : Label)
    (out : TargetBlockOutcome World) : TargetBlockOutcome World :=
  match out.flow with
  | .normal => ⟨.jumped entry, out.frame, out.state⟩
  | _ => out

theorem target_loop_backedge_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {body : List Instruction} {bound : Nat}
    (bounded : CodeJumpsWithin bound body) (entry : Label)
    (outside : targetAfterLabel? body entry = none)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (body ++ [.jump entry]) (body ++ [.jump entry])
        frame state out ↔
      ∃ inner, TargetRun interface heap calls result body body frame state inner ∧
        out = targetLoopBackedge entry inner := by
  have fresh : TopLabelsAbove bound [.jump entry] := by
    intro label member
    simp only [List.mem_singleton] at member
    cases member
  have appendedOutside : targetAfterLabel? (body ++ [.jump entry]) entry = none := by
    rw [after_label_append, outside]
    rfl
  rw [target_continuation_iff bounded bounded fresh]
  apply exists_congr
  rintro ⟨flow, after, post⟩
  apply and_congr_right
  intro innerRun
  cases flow with
  | normal =>
      constructor
      · intro continued
        cases continued with
        | normal ran => exact (target_outward_jump_run_exact _ entry appendedOutside after post out).mp ran
      · intro same
        exact .normal ((target_outward_jump_run_exact _ entry appendedOutside after post out).mpr same)
  | returned value =>
      exact ⟨fun continued => by cases continued; rfl,
        fun same => by cases same; exact .returned value after post⟩
  | jumped label =>
      exact ⟨fun continued => by cases continued; rfl,
        fun same => by cases same; exact .jumped label after post⟩

/-- The emitted while guard either skips the complete body and back edge,
or runs that actual tail. Earlier condition instructions are handled
separately; the guard itself introduces no visible label. -/
theorem target_loop_guard_tail_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {condition : NativeIR.Atom} {selected : Bool} {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state condition (.bool selected))
    (hscope : TemporariesScoped frame) (entry exit : Label) (body : List Instruction)
    (outside : targetAfterLabel? body exit = none) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result
      ([.branch (.negated condition) [.jump exit] []] ++ body ++ [.jump entry])
      ([.branch (.negated condition) [.jump exit] []] ++ body ++ [.jump entry])
      frame state out ↔
      if selected then
        TargetRun interface heap calls result (body ++ [.jump entry]) (body ++ [.jump entry])
          frame state out
      else out = ⟨.jumped exit, frame, state⟩ := by
  let guard := Instruction.branch (.negated condition) [.jump exit] []
  have free : TopLabelFree [guard] := by
    intro label member
    simp only [List.mem_singleton] at member
    dsimp [guard] at member
    cases member
  have absent : targetAfterLabel? ([guard] ++ (body ++ [.jump entry])) exit = none := by
    change targetAfterLabel? (body ++ [.jump entry]) exit = none
    rw [after_label_append, outside]
    rfl
  have guardExact := target_loop_guard_instruction_exact (heap := heap) (calls := calls)
    (result := result) read hscope exit
  change TargetRun interface heap calls result ([guard] ++ (body ++ [.jump entry]))
    ([guard] ++ (body ++ [.jump entry])) frame state out ↔ _
  cases selected with
  | true =>
      simp only [if_true]
      constructor
      · intro ran
        cases ran with
        | next first rest =>
            have same := (guardExact _).mp first
            simp only [if_true] at same
            cases same
            exact (target_label_free_prefix_root_iff free _ _ frame state out).mp rest
        | «return» first => have same := (guardExact _).mp first; cases same
        | resume first found rest => have same := (guardExact _).mp first; cases same
        | escape first missing => have same := (guardExact _).mp first; cases same
      · intro ran
        exact .next ((guardExact _).mpr rfl)
          ((target_label_free_prefix_root_iff free _ _ frame state out).mpr ran)
  | false =>
      simp only [Bool.false_eq_true, if_false]
      constructor
      · intro ran
        cases ran with
        | next first rest => have same := (guardExact _).mp first; cases same
        | «return» first => have same := (guardExact _).mp first; cases same
        | resume first found rest =>
            have same := (guardExact _).mp first
            simp only [Bool.false_eq_true, if_false] at same
            cases same
            rw [absent] at found
            cases found
        | escape first missing =>
            have same := (guardExact _).mp first
            simp only [Bool.false_eq_true, if_false] at same
            cases same
            rfl
      · intro same
        subst out
        exact .escape ((guardExact _).mpr rfl) absent

/-- One complete emitted iteration tail retains the actual selected body
outcome. Normal completion takes the back edge, while an existing return,
break or continue is not followed by another body instruction. -/
theorem target_loop_iteration_tail_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {earlier body : List Instruction} {bound : Nat}
    (prefixFree : TopLabelFree earlier) (bodyBound : CodeJumpsWithin bound body)
    {condition : NativeIR.Atom} {selected : Bool} {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state condition (.bool selected))
    (hscope : TemporariesScoped frame) (entry exit : Label)
    (entryOutside : targetAfterLabel? body entry = none)
    (exitOutside : targetAfterLabel? body exit = none) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result
      (earlier ++ ([.branch (.negated condition) [.jump exit] []] ++ body ++ [.jump entry]))
      ([.branch (.negated condition) [.jump exit] []] ++ body ++ [.jump entry])
      frame state out ↔
      if selected then
        ∃ inner, TargetRun interface heap calls result body body frame state inner ∧
          out = targetLoopBackedge entry inner
      else out = ⟨.jumped exit, frame, state⟩ := by
  rw [target_label_free_prefix_root_iff prefixFree]
  rw [target_loop_guard_tail_exact read hscope entry exit body exitOutside]
  cases selected
  · rfl
  · simpa only [if_true] using target_loop_backedge_exact bodyBound entry entryOutside frame state out

/-- Induction over the complete finite execution of the emitted scoped loop.
An entry transfer uses the strictly smaller actual resume spine. Every case
receives the original body derivation and the cleaned frame/state; no fuel,
replacement execution relation or assumed iteration count is introduced. -/
theorem target_scoped_loop_run_induction {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (entry exit : Label) (body : List Instruction)
    (P : TargetFrame → TargetState World → TargetBlockOutcome World → Prop)
    (normalCase : ∀ frame state inner,
      TargetRun interface heap calls result body body frame state inner → inner.flow = .normal →
      P frame state (targetCloseBlock frame inner))
    (returnedCase : ∀ frame state inner value,
      TargetRun interface heap calls result body body frame state inner → inner.flow = .returned value →
      P frame state (targetCloseBlock frame inner))
    (entryCase : ∀ frame state inner out,
      TargetRun interface heap calls result body body frame state inner → inner.flow = .jumped entry →
      P (targetCloseBlock frame inner).frame (targetCloseBlock frame inner).state out → P frame state out)
    (exitCase : ∀ frame state inner,
      TargetRun interface heap calls result body body frame state inner → inner.flow = .jumped exit →
      entry ≠ exit →
      P frame state ⟨.normal, (targetCloseBlock frame inner).frame, (targetCloseBlock frame inner).state⟩)
    (outwardCase : ∀ frame state inner label,
      TargetRun interface heap calls result body body frame state inner → inner.flow = .jumped label →
      entry ≠ label → exit ≠ label → P frame state (targetCloseBlock frame inner))
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result [.label entry, .scope body, .label exit]
      [.label entry, .scope body, .label exit] frame state out) : P frame state out := by
  let root := [Instruction.label entry, .scope body, .label exit]
  let tail := [Instruction.scope body, .label exit]
  let motive := fun fullRoot code frame state out =>
    fullRoot = root → (code = root ∨ code = tail) → P frame state out
  have complete : motive root root frame state out := by
    refine target_run_spine_induction (P := motive) ?_ ?_ ?_ ?_ ?_ ran
    · intro fullRoot frame state sameRoot sameCode
      rcases sameCode with impossible | impossible <;>
        dsimp [root, tail] at impossible <;> cases impossible
    · intro fullRoot rest first before middle pre post final head following ih sameRoot sameCode
      subst fullRoot
      rcases sameCode with whole | suffix
      · rcases List.cons.inj whole with ⟨rfl, rfl⟩
        cases head with
        | label => exact ih rfl (.inr rfl)
      · rcases List.cons.inj suffix with ⟨rfl, rfl⟩
        have single : TargetRun interface heap calls result [.scope body] [.scope body] before pre
            ⟨.normal, middle, post⟩ := .next head (.nil _ middle post)
        obtain ⟨inner, bodyRan, closed⟩ := (target_scope_body_exact body before pre _).mp single
        have normal : inner.flow = .normal := congrArg TargetBlockOutcome.flow closed.symm
        have endpoint : final = ⟨.normal, middle, post⟩ :=
          (target_run_empty_exact root middle post final).mp
            ((target_label_cons_exact root exit [] middle post final).mp following)
        subst final
        rw [closed]
        exact normalCase before pre inner bodyRan normal
    · intro fullRoot rest first value before after pre post head sameRoot sameCode
      subst fullRoot
      rcases sameCode with whole | suffix
      · rcases List.cons.inj whole with ⟨rfl, rfl⟩
        cases head
      · rcases List.cons.inj suffix with ⟨rfl, rfl⟩
        have single : TargetRun interface heap calls result [.scope body] [.scope body] before pre
            ⟨.returned value, after, post⟩ := .return head
        obtain ⟨inner, bodyRan, closed⟩ := (target_scope_body_exact body before pre _).mp single
        have returned : inner.flow = .returned value := congrArg TargetBlockOutcome.flow closed.symm
        rw [closed]
        exact returnedCase before pre inner value bodyRan returned
    · intro fullRoot rest suffix first label before middle pre post final head found following ih sameRoot sameCode
      subst fullRoot
      rcases sameCode with whole | codeTail
      · rcases List.cons.inj whole with ⟨rfl, rfl⟩
        cases head
      · rcases List.cons.inj codeTail with ⟨rfl, rfl⟩
        have single : TargetRun interface heap calls result [.scope body] [.scope body] before pre
            ⟨.jumped label, middle, post⟩ := .escape head rfl
        obtain ⟨inner, bodyRan, closed⟩ := (target_scope_body_exact body before pre _).mp single
        have jumped : inner.flow = .jumped label := congrArg TargetBlockOutcome.flow closed.symm
        by_cases entered : entry = label
        · subst label
          have lookup : targetAfterLabel? root entry = some tail := by simp only [root, tail, targetAfterLabel?, if_true]
          have sameSuffix : suffix = tail := (Option.some.inj (lookup.symm.trans found)).symm
          subst suffix
          apply entryCase before pre inner final bodyRan jumped
          rw [← closed]
          exact ih rfl (.inr rfl)
        · by_cases exited : exit = label
          · subst label
            have lookup : targetAfterLabel? root exit = some [] := by
              simp only [root, targetAfterLabel?, entered, if_false, if_true]
            have empty : suffix = [] := (Option.some.inj (lookup.symm.trans found)).symm
            subst suffix
            have endpoint := (target_run_empty_exact root middle post final).mp following
            subst final
            have finished := exitCase before pre inner bodyRan jumped entered
            simpa only [← closed] using finished
          · have lookup : targetAfterLabel? root label = none := by
              simp only [root, targetAfterLabel?, entered, exited, if_false]
            rw [lookup] at found
            cases found
    · intro fullRoot rest first label before after pre post head outside sameRoot sameCode
      subst fullRoot
      rcases sameCode with whole | suffix
      · rcases List.cons.inj whole with ⟨rfl, rfl⟩
        cases head
      · rcases List.cons.inj suffix with ⟨rfl, rfl⟩
        have single : TargetRun interface heap calls result [.scope body] [.scope body] before pre
            ⟨.jumped label, after, post⟩ := .escape head rfl
        obtain ⟨inner, bodyRan, closed⟩ := (target_scope_body_exact body before pre _).mp single
        have jumped : inner.flow = .jumped label := congrArg TargetBlockOutcome.flow closed.symm
        have entered : entry ≠ label := by
          intro same
          simp only [root, targetAfterLabel?, same, if_true] at outside
          cases outside
        have exited : exit ≠ label := by
          intro same
          simp only [root, targetAfterLabel?, entered, same, if_false, if_true] at outside
          cases outside
        rw [closed]
        exact outwardCase before pre inner label bodyRan jumped entered exited
  exact complete rfl (.inl rfl)

/-- An actual entry transfer repeats only after closing the iteration scope. -/
theorem target_scoped_loop_repeat {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {entry exit : Label} {body : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {inner out : TargetBlockOutcome World}
    (iteration : TargetRun interface heap calls result body body frame state inner)
    (entered : inner.flow = .jumped entry)
    (following : TargetRun interface heap calls result [.label entry, .scope body, .label exit]
      [.label entry, .scope body, .label exit] (targetCloseBlock frame inner).frame
      (targetCloseBlock frame inner).state out) :
    TargetRun interface heap calls result [.label entry, .scope body, .label exit]
      [.label entry, .scope body, .label exit] frame state out := by
  apply (target_scoped_loop_iteration_exact entry exit body frame state out).mpr
  refine ⟨inner, iteration, ?_⟩
  simp only [entered, if_true]
  exact (target_label_cons_exact _ _ _ _ _ _).mp following

/-- An actual exit transfer closes the scope and finishes normally. -/
theorem target_scoped_loop_exit {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {entry exit : Label} {body : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {inner : TargetBlockOutcome World}
    (iteration : TargetRun interface heap calls result body body frame state inner)
    (exited : inner.flow = .jumped exit) (different : entry ≠ exit) :
    TargetRun interface heap calls result [.label entry, .scope body, .label exit]
      [.label entry, .scope body, .label exit] frame state
      ⟨.normal, (targetCloseBlock frame inner).frame, (targetCloseBlock frame inner).state⟩ := by
  apply (target_scoped_loop_iteration_exact entry exit body frame state _).mpr
  exact ⟨inner, iteration, by simp only [exited, different, if_false, if_true]⟩

/-- An actual return leaves the loop with its complete cleaned outcome. -/
theorem target_scoped_loop_return {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {entry exit : Label} {body : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {inner : TargetBlockOutcome World} {value : TargetValue}
    (iteration : TargetRun interface heap calls result body body frame state inner)
    (returned : inner.flow = .returned value) :
    TargetRun interface heap calls result [.label entry, .scope body, .label exit]
      [.label entry, .scope body, .label exit] frame state (targetCloseBlock frame inner) := by
  apply (target_scoped_loop_iteration_exact entry exit body frame state _).mpr
  exact ⟨inner, iteration, by simp only [returned]⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
