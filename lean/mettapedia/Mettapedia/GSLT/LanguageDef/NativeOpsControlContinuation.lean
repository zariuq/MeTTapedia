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
  def CodeJumpsWithin (bound : Nat) : List Instruction → Prop
    | [] => True
    | first :: rest => InstructionJumpsWithin bound first ∧ CodeJumpsWithin bound rest
  termination_by code => sizeOf code
  decreasing_by all_goals simp_wf; all_goals omega

  def InstructionJumpsWithin (bound : Nat) : Instruction → Prop
    | .jump label => label.identity ≤ bound
    | .scope body | .forWord _ _ body => CodeJumpsWithin bound body
    | .branch _ yes no => CodeJumpsWithin bound yes ∧ CodeJumpsWithin bound no
    | .switch _ arms otherwise => ArmJumpsWithin bound arms ∧ CodeJumpsWithin bound otherwise
    | _ => True
  termination_by instruction => sizeOf instruction
  decreasing_by all_goals simp_wf; all_goals omega

  def ArmJumpsWithin (bound : Nat) : List (BitVec 64 × List Instruction) → Prop
    | [] => True
    | (_, body) :: rest => CodeJumpsWithin bound body ∧ ArmJumpsWithin bound rest
  termination_by arms => sizeOf arms
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- Only labels visible to the current root are constrained. Nested roots
    are checked separately, as in TargetInstructionEval. -/
def TopLabelsAbove (bound : Nat) (code : List Instruction) : Prop :=
  ∀ label, Instruction.label label ∈ code → bound < label.identity

theorem code_jumps_within_append (bound : Nat) (first second : List Instruction) :
    CodeJumpsWithin bound (first ++ second) ↔
      CodeJumpsWithin bound first ∧ CodeJumpsWithin bound second := by
  induction first with
  | nil => simp only [List.nil_append, CodeJumpsWithin, true_and]
  | cons head tail ih =>
      simp only [List.cons_append, CodeJumpsWithin, ih, and_assoc]

theorem arm_jumps_within_cons (bound : Nat) (arm : BitVec 64 × List Instruction)
    (rest : List (BitVec 64 × List Instruction)) :
    ArmJumpsWithin bound (arm :: rest) ↔
      CodeJumpsWithin bound arm.2 ∧ ArmJumpsWithin bound rest := by
  cases arm
  simp only [ArmJumpsWithin]

theorem jump_free_arms_cons (arm : BitVec 64 × List Instruction)
    (rest : List (BitVec 64 × List Instruction)) :
    jumpFreeArms (arm :: rest) = (jumpFreeCode arm.2 && jumpFreeArms rest) := by
  cases arm
  simp only [jumpFreeArms]

mutual
  theorem code_jumps_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
      {code : List Instruction} (bounded : CodeJumpsWithin lower code) : CodeJumpsWithin upper code := by
    cases code with
    | nil => simp only [CodeJumpsWithin]
    | cons first rest =>
        simp only [CodeJumpsWithin] at bounded ⊢
        exact ⟨instruction_jumps_within_weaken inside bounded.1,
          code_jumps_within_weaken inside bounded.2⟩
  termination_by sizeOf code
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem instruction_jumps_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
      {instruction : Instruction} (bounded : InstructionJumpsWithin lower instruction) :
      InstructionJumpsWithin upper instruction := by
    cases instruction <;> simp only [InstructionJumpsWithin] at bounded ⊢
    all_goals first
      | exact bounded.trans inside
      | exact code_jumps_within_weaken inside bounded
      | exact ⟨code_jumps_within_weaken inside bounded.1, code_jumps_within_weaken inside bounded.2⟩
      | exact ⟨arm_jumps_within_weaken inside bounded.1, code_jumps_within_weaken inside bounded.2⟩
  termination_by sizeOf instruction
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem arm_jumps_within_weaken {lower upper : Nat} (inside : lower ≤ upper)
      {arms : List (BitVec 64 × List Instruction)} (bounded : ArmJumpsWithin lower arms) :
      ArmJumpsWithin upper arms := by
    cases arms with
    | nil => simp only [ArmJumpsWithin]
    | cons arm rest =>
        rw [arm_jumps_within_cons] at bounded ⊢
        exact ⟨code_jumps_within_weaken inside bounded.1, arm_jumps_within_weaken inside bounded.2⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals first | omega | (cases arm; simp_all; omega)
end

mutual
  theorem jump_free_code_within (bound : Nat) {code : List Instruction}
      (checked : jumpFreeCode code = true) : CodeJumpsWithin bound code := by
    cases code with
    | nil => simp only [CodeJumpsWithin]
    | cons first rest =>
        simp only [jumpFreeCode, Bool.and_eq_true] at checked
        simp only [CodeJumpsWithin]
        exact ⟨jump_free_instruction_within bound checked.1, jump_free_code_within bound checked.2⟩
  termination_by sizeOf code
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem jump_free_instruction_within (bound : Nat) {instruction : Instruction}
      (checked : jumpFreeInstruction instruction = true) : InstructionJumpsWithin bound instruction := by
    cases instruction <;> simp only [jumpFreeInstruction, InstructionJumpsWithin,
      Bool.and_eq_true, Bool.false_eq_true] at checked ⊢
    all_goals first
      | exact jump_free_code_within bound checked
      | exact ⟨jump_free_code_within bound checked.1, jump_free_code_within bound checked.2⟩
      | exact ⟨jump_free_arms_within bound checked.1, jump_free_code_within bound checked.2⟩
  termination_by sizeOf instruction
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem jump_free_arms_within (bound : Nat) {arms : List (BitVec 64 × List Instruction)}
      (checked : jumpFreeArms arms = true) : ArmJumpsWithin bound arms := by
    cases arms with
    | nil => simp only [ArmJumpsWithin]
    | cons arm rest =>
        rw [jump_free_arms_cons, Bool.and_eq_true] at checked
        rw [arm_jumps_within_cons]
        exact ⟨jump_free_code_within bound checked.1, jump_free_arms_within bound checked.2⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals first | omega | (cases arm; simp_all; omega)
end

theorem after_label_suffix_within {bound : Nat} {code suffix : List Instruction} {label : Label}
    (bounded : CodeJumpsWithin bound code) (found : targetAfterLabel? code label = some suffix) :
    CodeJumpsWithin bound suffix := by
  induction code with
  | nil => cases found
  | cons head tail ih =>
      simp only [CodeJumpsWithin] at bounded
      have tailBound := bounded.2
      cases head <;> simp only [targetAfterLabel?] at found
      all_goals first
        | exact ih tailBound found
        | split at found
          · cases Option.some.inj found
            exact tailBound
          · exact ih tailBound found

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

theorem fresh_continuation_lookup {bound : Nat} (root continuation : List Instruction)
    (fresh : TopLabelsAbove bound continuation) (label : Label) (earlier : label.identity ≤ bound) :
    targetAfterLabel? (root ++ continuation) label =
      (targetAfterLabel? root label).map (fun suffix => suffix ++ continuation) := by
  rw [after_label_append]
  cases targetAfterLabel? root label with
  | none => exact after_label_none_of_above fresh earlier
  | some suffix => rfl

theorem within_selected_case {bound : Nat} (value : BitVec 64)
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
    (armBound : ArmJumpsWithin bound arms) (otherwiseBound : CodeJumpsWithin bound otherwise) :
    CodeJumpsWithin bound (targetSelectCase value arms otherwise) := by
  induction arms with
  | nil => simpa only [targetSelectCase, List.find?_nil] using otherwiseBound
  | cons arm rest ih =>
      rcases arm with ⟨selector, body⟩
      simp only [ArmJumpsWithin] at armBound
      by_cases same : selector == value
      · simpa [targetSelectCase, same] using armBound.1
      · simpa [targetSelectCase, same] using ih armBound.2

local macro "bounded_execution_cases" : tactic => `(tactic| (
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
    simp only [InstructionJumpsWithin] at checked
    exact ih label checked jumped
  case branch =>
    rename_i tested selected ih label checked jumped
    simp only [InstructionJumpsWithin] at checked
    apply ih label ?_ ?_ jumped
    all_goals split <;> first | exact checked.1 | exact checked.2
  case switch =>
    rename_i value selected ih label checked jumped
    simp only [InstructionJumpsWithin] at checked
    apply ih label ?_ ?_ jumped
    all_goals exact within_selected_case _ checked.1 checked.2
  case scope =>
    rename_i ran ih label checked jumped
    simp only [InstructionJumpsWithin] at checked
    exact ih label checked checked jumped
  case label => rename_i label checked jumped; cases jumped
  case jump =>
    rename_i label checked jumped
    simp only [InstructionJumpsWithin] at checked
    cases jumped
    exact checked
  case «return» => rename_i label checked jumped; cases jumped
  case nil => rename_i label rootBound checked jumped; cases jumped
  case next =>
    rename_i first rest ihFirst ihRest label rootBound checked jumped
    simp only [CodeJumpsWithin] at checked
    exact ihRest label rootBound checked.2 jumped
  case «return» => rename_i label rootBound checked jumped; cases jumped
  case resume =>
    rename_i first found rest ihFirst ihRest label rootBound checked jumped
    exact ihRest label rootBound (after_label_suffix_within rootBound found) jumped
  case escape =>
    rename_i first outside ih label rootBound checked jumped
    simp only [CodeJumpsWithin] at checked
    exact ih label checked.1 jumped
  case done => rename_i label checked jumped; cases jumped
  case next =>
    rename_i readCounter readBound within ran normal counterAfter rest ihRun ihRest label checked jumped
    exact ihRest label checked jumped
  case stop =>
    rename_i readCounter readBound within ran abrupt ih label checked jumped
    exact ih label checked checked jumped))

theorem instruction_jump_within {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {bound : Nat}
    (ran : TargetInstructionEval interface heap calls result instruction frame state out) :
    ∀ label, InstructionJumpsWithin bound instruction → out.flow = .jumped label → label.identity ≤ bound := by
  induction ran using TargetInstructionEval.rec
    (motive_2 := fun root code _ _ out _ =>
      ∀ label, CodeJumpsWithin bound root → CodeJumpsWithin bound code →
        out.flow = .jumped label → label.identity ≤ bound)
    (motive_3 := fun _ _ body _ _ out _ =>
      ∀ label, CodeJumpsWithin bound body → out.flow = .jumped label → label.identity ≤ bound)
  bounded_execution_cases

theorem run_jump_within {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root code : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World} {bound : Nat}
    (ran : TargetRun interface heap calls result root code frame state out) :
    ∀ label, CodeJumpsWithin bound root → CodeJumpsWithin bound code →
      out.flow = .jumped label → label.identity ≤ bound := by
  induction ran using TargetRun.rec
    (motive_1 := fun instruction _ _ out _ =>
      ∀ label, InstructionJumpsWithin bound instruction → out.flow = .jumped label → label.identity ≤ bound)
    (motive_3 := fun _ _ body _ _ out _ =>
      ∀ label, CodeJumpsWithin bound body → out.flow = .jumped label → label.identity ≤ bound)
  bounded_execution_cases

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
      simp only [CodeJumpsWithin] at codeBound
      exact .next firstRun (ih rootBound codeBound.2 fresh following)
    · intro root rest first value before after pre post firstRun continuation bound rootBound codeBound
        fresh out following
      cases following
      exact .return firstRun
    · intro root rest suffix first label before middle pre post final firstRun found restRun ih continuation
        bound rootBound codeBound fresh out following
      simp only [CodeJumpsWithin] at codeBound
      have within := instruction_jump_within firstRun label codeBound.1 rfl
      have extended := fresh_continuation_lookup root continuation fresh label within
      rw [found, Option.map_some] at extended
      exact .resume firstRun extended (ih rootBound (after_label_suffix_within rootBound found) fresh following)
    · intro root rest first label before after pre post firstRun outside continuation bound rootBound codeBound
        fresh out following
      simp only [CodeJumpsWithin] at codeBound
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
          simp only [CodeJumpsWithin] at codeBound
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
          simp only [CodeJumpsWithin] at codeBound
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
          simp only [CodeJumpsWithin] at codeBound
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
  theorem local_control_statement_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {statement : Statement}
      (supported : SourceLocalControlStatement statement) {supply : NativeIR.Supply}
      {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.statement? interface result loops scope statement supply = some output) :
      supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
        TopLabelsAbove supply.next output.code := by
    cases supported with
    | declare name type child =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := declaration_lowering_exact compiled
        subst output
        refine ⟨(short_circuit_lowering_bounds child lowered).1.le, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨short_circuit_top_labels_above child lowered _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | set name child =>
        obtain ⟨type, value, _, _, lowered, same⟩ := local_set_lowering_exact compiled
        subst output
        refine ⟨(short_circuit_lowering_bounds child lowered).1.le, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨short_circuit_top_labels_above child lowered _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | branch tested yes no =>
        obtain ⟨nextScope, test, whenTrue, whenFalse, _, testCompiled, yesCompiled, noCompiled, same⟩ :=
          branch_lowering_exact compiled
        have testBound := (short_circuit_lowering_bounds tested testCompiled).1.le
        have yesBounds := local_control_block_bounds yes (loop_labels_within_weaken testBound bounded) yesCompiled
        have noBounds := local_control_block_bounds no
          (loop_labels_within_weaken yesBounds.1 (loop_labels_within_weaken testBound bounded)) noCompiled
        subst output
        refine ⟨testBound.trans (yesBounds.1.trans noBounds.1), ?_, ?_⟩
        · apply (code_jumps_within_append _ _ _).mpr
          refine ⟨expression_jumps_within testCompiled _, ?_⟩
          simp only [CodeJumpsWithin, InstructionJumpsWithin]
          exact ⟨⟨code_jumps_within_weaken noBounds.1 yesBounds.2.1, noBounds.2.1⟩, True.intro⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨short_circuit_top_labels_above tested testCompiled _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | «while» tested body =>
        obtain ⟨nextScope, test, iteration, _, testCompiled, bodyCompiled, same⟩ := while_lowering_exact compiled
        have testBound := (short_circuit_lowering_bounds tested testCompiled).1.le
        have bodyBounds := local_control_block_bounds body
          (loop_labels_within_weaken testBound (fresh_loop_labels_within supply bounded)) bodyCompiled
        have exitBound : (freshLoopLabels supply).exit.identity ≤ iteration.supply.next :=
          testBound.trans bodyBounds.1
        have entryBound : (freshLoopLabels supply).entry.identity ≤ iteration.supply.next :=
          (fresh_loop_labels_above_supply supply).2.le.trans exitBound
        subst output
        refine ⟨?_, ?_, ?_⟩
        · exact (NativeIR.fresh_strict supply).le.trans
            ((NativeIR.fresh_strict (NativeIR.fresh supply).2).le.trans (testBound.trans bodyBounds.1))
        · simp only [CodeJumpsWithin, InstructionJumpsWithin]
          refine ⟨True.intro, ?_, True.intro, True.intro⟩
          apply (code_jumps_within_append _ _ _).mpr
          refine ⟨(code_jumps_within_append _ _ _).mpr ⟨?_, bodyBounds.2.1⟩, ?_⟩
          · apply (code_jumps_within_append _ _ _).mpr
            refine ⟨expression_jumps_within testCompiled _, ?_⟩
            simp only [CodeJumpsWithin, InstructionJumpsWithin]
            exact ⟨⟨⟨exitBound, True.intro⟩, True.intro⟩, True.intro⟩
          · simpa only [CodeJumpsWithin, InstructionJumpsWithin] using And.intro entryBound True.intro
        · intro label member
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
          rcases member with entry | impossible | exit
          · cases Instruction.label.inj entry
            exact (fresh_loop_labels_above_supply supply).1
          · cases impossible
          · cases Instruction.label.inj exit
            exact (fresh_loop_labels_above_supply supply).1.trans (fresh_loop_labels_above_supply supply).2
    | «break» =>
        obtain ⟨active, outer, same, outputSame⟩ := break_lowering_exact compiled
        subst loops
        subst output
        refine ⟨Nat.le_refl _, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, InstructionJumpsWithin] using
          And.intro (bounded active (List.mem_cons_self)).2 True.intro
    | «continue» =>
        obtain ⟨active, outer, same, outputSame⟩ := continue_lowering_exact compiled
        subst loops
        subst output
        refine ⟨Nat.le_refl _, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, InstructionJumpsWithin] using
          And.intro (bounded active (List.mem_cons_self)).1 True.intro
    | effect child =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := effect_lowering_exact compiled
        subst output
        exact ⟨(short_circuit_lowering_bounds child lowered).1.le, expression_jumps_within lowered _,
          short_circuit_top_labels_above child lowered _⟩
    | returnUnit =>
        obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
        subst output
        exact ⟨Nat.le_refl _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial,
          top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | returnValue child =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := return_value_lowering_exact compiled
        subst output
        refine ⟨(short_circuit_lowering_bounds child lowered).1.le, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨short_circuit_top_labels_above child lowered _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | block child =>
        obtain ⟨nextScope, body, _, lowered, same⟩ := block_statement_lowering_exact compiled
        have bodyBounds := local_control_block_bounds child bounded lowered
        subst output
        refine ⟨bodyBounds.1, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, InstructionJumpsWithin] using And.intro bodyBounds.2.1 True.intro
  termination_by sizeOf statement
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem local_control_block_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {body : List Statement}
      (supported : SourceLocalControlBlock body) {supply : NativeIR.Supply}
      {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.block? interface result loops scope body supply = some output) :
      supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
        TopLabelsAbove supply.next output.code := by
    cases supported with
    | nil =>
        rw [NativeLowering.block?] at compiled
        cases Option.some.inj compiled
        exact ⟨Nat.le_refl _, by simp only [CodeJumpsWithin], top_labels_above_nil _⟩
    | cons head tail =>
        obtain ⟨first, rest, firstCompiled, restCompiled, same⟩ := block_cons_lowering_exact compiled
        have firstBounds := local_control_statement_bounds head bounded firstCompiled
        have restBounds := local_control_block_bounds tail
          (loop_labels_within_weaken firstBounds.1 bounded) restCompiled
        subst output
        exact ⟨firstBounds.1.trans restBounds.1,
          (code_jumps_within_append _ _ _).mpr
            ⟨code_jumps_within_weaken restBounds.1 firstBounds.2.1, restBounds.2.1⟩,
          (top_labels_above_append _ _ _).mpr
            ⟨firstBounds.2.2, top_labels_above_weaken firstBounds.1 restBounds.2.2⟩⟩
  termination_by sizeOf body
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

end Mettapedia.GSLT.LanguageDef.NativeOps
