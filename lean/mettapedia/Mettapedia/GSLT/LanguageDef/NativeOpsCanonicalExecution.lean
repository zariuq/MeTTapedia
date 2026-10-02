import Mettapedia.GSLT.LanguageDef.NativeOpsTargetFunctions
import Mettapedia.GSLT.LanguageDef.NativeOpsZeroNormalization

/-!
# Typed initializer normalization throughout native execution

Scalar C initializers have a checked pure normalization. The control laws
below carry that normalization through finite target execution, retaining
the same raw return, scoped frame and complete operational state. Labels,
loop counters, calls and memory effects retain their original order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction)

theorem canonical_after_label (code : List Instruction) (label : NativeIR.Label) :
    targetAfterLabel? (canonicalCode code) label =
      (targetAfterLabel? code label).map canonicalCode := by
  induction code with
  | nil => simp only [canonicalCode, targetAfterLabel?, Option.map_none]
  | cons first rest ih =>
      cases first <;>
        simp only [canonicalCode, canonicalInstruction, targetAfterLabel?, ih]
      case label found =>
        split <;> simp_all

theorem canonical_selected_case (value : BitVec 64)
    (arms : List (BitVec 64 × List Instruction)) (otherwise : List Instruction) :
    targetSelectCase value (canonicalArms arms) (canonicalCode otherwise) =
      canonicalCode (targetSelectCase value arms otherwise) := by
  induction arms with
  | nil => simp only [canonicalArms, targetSelectCase, List.find?_nil]
  | cons arm rest ih =>
      rcases arm with ⟨selector, body⟩
      by_cases same : selector == value
      · simp [targetSelectCase, canonicalArms, same]
      · simp [targetSelectCase, canonicalArms, same] at ih ⊢
        exact ih

local macro "canonical_forward_cases" : tactic => `(tactic| (
  all_goals intros
  all_goals try simp only [canonicalInstruction, canonicalCode]
  case temporary =>
    rename_i unused computed
    exact .temporary unused ((canonical_pure_exact _ _ _ _ _).mpr computed)
  case assign => exact .assign (by assumption) (by assumption)
  case helper => exact .helper (by assumption) (by assumption)
  case call => exact .call (by assumption) (by assumption) (by assumption)
  case contextExists => exact .contextExists _ _
  case contextClear => exact .contextClear (by assumption)
  case contextFault => exact .contextFault (by assumption) (by assumption)
  case numericClear => exact .numericClear (by assumption) (by assumption)
  case numericFault => exact .numericFault (by assumption) (by assumption) (by assumption)
  case declareLocal => exact .declareLocal (by assumption)
  case write => exact .write (by assumption) (by assumption) (by assumption)
  case writeElement =>
    exact .writeElement (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption)
  case forWord =>
    rename_i unused loop ih
    exact .forWord unused ih
  case branch =>
    rename_i tested selected ih
    apply TargetInstructionEval.branch tested
    simpa only [apply_ite canonicalCode] using ih
  case switch =>
    rename_i read selected ih
    apply TargetInstructionEval.switch read
    simpa only [canonical_selected_case] using ih
  case scope =>
    rename_i ran ih
    exact .scope ih
  case label => exact .label _ _ _
  case jump => exact .jump _ _ _
  case «return» => exact .return (by assumption)
  case nil => exact .nil _ _ _
  case next =>
    rename_i first rest ihFirst ihRest
    exact .next ihFirst ihRest
  case «return» =>
    exact .return (by assumption)
  case resume =>
    rename_i first found rest ihFirst ihRest
    exact .resume ihFirst (by rw [canonical_after_label, found]; rfl) ihRest
  case escape =>
    rename_i first outside ih
    exact .escape ih (by rw [canonical_after_label, outside]; rfl)
  case done => exact .done (by assumption) (by assumption) (by assumption)
  case next =>
    exact .next (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)
  case stop =>
    rename_i readCounter readBound within ran abrupt ih
    exact .stop readCounter readBound within ih abrupt))

theorem canonical_instruction_forward {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetInstructionEval interface heap calls result instruction frame state out) :
    TargetInstructionEval interface heap calls result (canonicalInstruction instruction) frame state out := by
    induction ran using TargetInstructionEval.rec
      (motive_2 := fun root remaining frame state out _ =>
        TargetRun interface heap calls result (canonicalCode root) (canonicalCode remaining) frame state out)
      (motive_3 := fun counter bound body frame state out _ =>
        TargetForEval interface heap calls result counter bound (canonicalCode body) frame state out)
    canonical_forward_cases

theorem canonical_run_forward {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root remaining : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root remaining frame state out) :
    TargetRun interface heap calls result (canonicalCode root) (canonicalCode remaining) frame state out := by
    induction ran using TargetRun.rec
      (motive_1 := fun instruction frame state out _ =>
        TargetInstructionEval interface heap calls result (canonicalInstruction instruction) frame state out)
      (motive_3 := fun counter bound body frame state out _ =>
        TargetForEval interface heap calls result counter bound (canonicalCode body) frame state out)
    canonical_forward_cases

theorem canonical_for_forward {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {counter : Nat} {bound : NativeIR.Atom} {body : List Instruction}
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetForEval interface heap calls result counter bound body frame state out) :
    TargetForEval interface heap calls result counter bound (canonicalCode body) frame state out := by
    induction ran using TargetForEval.rec
      (motive_1 := fun instruction frame state out _ =>
        TargetInstructionEval interface heap calls result (canonicalInstruction instruction) frame state out)
      (motive_2 := fun root remaining frame state out _ =>
        TargetRun interface heap calls result (canonicalCode root) (canonicalCode remaining) frame state out)

    canonical_forward_cases

private theorem canonical_nil_preimage {code : List Instruction}
    (equal : [] = canonicalCode code) : code = [] := by
  cases code with
  | nil => rfl
  | cons first rest =>
      simp only [canonicalCode] at equal
      cases equal

private theorem canonical_cons_preimage {first : Instruction} {rest code : List Instruction}
    (equal : first :: rest = canonicalCode code) :
    ∃ originalFirst originalRest, code = originalFirst :: originalRest ∧
      first = canonicalInstruction originalFirst ∧ rest = canonicalCode originalRest := by
  cases code with
  | nil => simp only [canonicalCode, List.cons_ne_nil] at equal
  | cons originalFirst originalRest =>
      simp only [canonicalCode, List.cons.injEq] at equal
      exact ⟨originalFirst, originalRest, rfl, equal.1, equal.2⟩

private theorem canonical_label_preimage {root original : List Instruction}
    {label : NativeIR.Label} {suffix : List Instruction}
    (equal : root = canonicalCode original) (found : targetAfterLabel? root label = some suffix) :
    ∃ originalSuffix, targetAfterLabel? original label = some originalSuffix ∧
      suffix = canonicalCode originalSuffix := by
  rw [equal, canonical_after_label] at found
  cases lookup : targetAfterLabel? original label with
  | none =>
      simp only [lookup, Option.map_none] at found
      cases found
  | some originalSuffix =>
      simp only [lookup, Option.map_some, Option.some.injEq] at found
      exact ⟨originalSuffix, rfl, found.symm⟩

private theorem canonical_label_none {root original : List Instruction} {label : NativeIR.Label}
    (equal : root = canonicalCode original) (outside : targetAfterLabel? root label = none) :
    targetAfterLabel? original label = none := by
  rw [equal, canonical_after_label] at outside
  cases lookup : targetAfterLabel? original label with
  | none => rfl
  | some suffix =>
      simp only [lookup, Option.map_some] at outside
      cases outside

local macro "restore_canonical_instruction" : tactic => `(tactic| (
  rename_i original equal
  cases original <;> simp only [canonicalInstruction] at equal <;> cases equal))

local macro "canonical_backward_cases" : tactic => `(tactic| (
  all_goals intros
  case temporary =>
    rename_i unused computed original equal
    cases original <;> simp only [canonicalInstruction] at equal <;> cases equal
    exact .temporary unused ((canonical_pure_exact _ _ _ _ _).mp computed)
  case assign =>
    restore_canonical_instruction
    exact .assign (by assumption) (by assumption)
  case helper =>
    restore_canonical_instruction
    exact .helper (by assumption) (by assumption)
  case call =>
    restore_canonical_instruction
    exact .call (by assumption) (by assumption) (by assumption)
  case contextExists =>
    restore_canonical_instruction
    exact .contextExists _ _
  case contextClear =>
    restore_canonical_instruction
    exact .contextClear (by assumption)
  case contextFault =>
    restore_canonical_instruction
    exact .contextFault (by assumption) (by assumption)
  case numericClear =>
    restore_canonical_instruction
    exact .numericClear (by assumption) (by assumption)
  case numericFault =>
    restore_canonical_instruction
    exact .numericFault (by assumption) (by assumption) (by assumption)
  case declareLocal =>
    restore_canonical_instruction
    exact .declareLocal (by assumption)
  case write =>
    restore_canonical_instruction
    exact .write (by assumption) (by assumption) (by assumption)
  case writeElement =>
    restore_canonical_instruction
    exact .writeElement (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption)
  case forWord =>
    rename_i unused loop ih original equal
    cases original <;> simp only [canonicalInstruction] at equal <;> cases equal
    exact .forWord unused (ih _ rfl)
  case branch =>
    rename_i tested selected ih original equal
    cases original <;> simp only [canonicalInstruction] at equal <;> cases equal
    apply TargetInstructionEval.branch tested
    apply ih _ _ <;> simp only [apply_ite canonicalCode]
  case switch =>
    rename_i read selected ih original equal
    cases original <;> simp only [canonicalInstruction] at equal <;> cases equal
    apply TargetInstructionEval.switch read
    apply ih _ _ <;> exact canonical_selected_case _ _ _
  case scope =>
    rename_i ran ih original equal
    cases original <;> simp only [canonicalInstruction] at equal <;> cases equal
    exact .scope (ih _ _ rfl rfl)
  case label =>
    restore_canonical_instruction
    exact .label _ _ _
  case jump =>
    restore_canonical_instruction
    exact .jump _ _ _
  case «return» =>
    restore_canonical_instruction
    exact .return (by assumption)
  case nil =>
    rename_i originalRoot originalRemaining rootEq remainingEq
    have empty := canonical_nil_preimage remainingEq
    subst originalRemaining
    exact .nil _ _ _
  case next =>
    rename_i first rest ihFirst ihRest originalRoot originalRemaining rootEq remainingEq
    rcases canonical_cons_preimage remainingEq with
      ⟨originalFirst, originalRest, codeEq, firstEq, restEq⟩
    rw [codeEq]
    exact .next (ihFirst originalFirst firstEq) (ihRest originalRoot originalRest rootEq restEq)
  case «return» =>
    rename_i first ih originalRoot originalRemaining rootEq remainingEq
    rcases canonical_cons_preimage remainingEq with
      ⟨originalFirst, originalRest, codeEq, firstEq, restEq⟩
    rw [codeEq]
    exact .return (ih originalFirst firstEq)
  case resume =>
    rename_i first found rest ihFirst ihRest originalRoot originalRemaining rootEq remainingEq
    rcases canonical_cons_preimage remainingEq with
      ⟨originalFirst, originalRest, codeEq, firstEq, restEq⟩
    rw [codeEq]
    rcases canonical_label_preimage rootEq found with ⟨originalSuffix, lookup, suffixEq⟩
    exact .resume (ihFirst originalFirst firstEq) lookup
      (ihRest originalRoot originalSuffix rootEq suffixEq)
  case escape =>
    rename_i first outside ih originalRoot originalRemaining rootEq remainingEq
    rcases canonical_cons_preimage remainingEq with
      ⟨originalFirst, originalRest, codeEq, firstEq, restEq⟩
    rw [codeEq]
    exact .escape (ih originalFirst firstEq) (canonical_label_none rootEq outside)
  case done => exact .done (by assumption) (by assumption) (by assumption)
  case next =>
    rename_i readCounter readBound within ran normal counterAfter rest ihRun ihRest original equal
    exact .next readCounter readBound within (ihRun original original equal equal)
      normal counterAfter (ihRest original equal)
  case stop =>
    rename_i readCounter readBound within ran abrupt ih original equal
    exact .stop readCounter readBound within (ih original original equal equal) abrupt))

theorem canonical_instruction_reflect {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetInstructionEval interface heap calls result instruction frame state out) :
    ∀ original, instruction = canonicalInstruction original →
      TargetInstructionEval interface heap calls result original frame state out := by
    induction ran using TargetInstructionEval.rec
      (motive_2 := fun root remaining frame state out _ => ∀ originalRoot originalRemaining,
        root = canonicalCode originalRoot → remaining = canonicalCode originalRemaining →
        TargetRun interface heap calls result originalRoot originalRemaining frame state out)
      (motive_3 := fun counter bound body frame state out _ => ∀ original,
        body = canonicalCode original →
        TargetForEval interface heap calls result counter bound original frame state out)
    canonical_backward_cases

theorem canonical_run_reflect {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root remaining : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root remaining frame state out) :
    ∀ originalRoot originalRemaining, root = canonicalCode originalRoot →
      remaining = canonicalCode originalRemaining →
      TargetRun interface heap calls result originalRoot originalRemaining frame state out := by
    induction ran using TargetRun.rec
      (motive_1 := fun instruction frame state out _ => ∀ original,
        instruction = canonicalInstruction original →
        TargetInstructionEval interface heap calls result original frame state out)
      (motive_3 := fun counter bound body frame state out _ => ∀ original,
        body = canonicalCode original →
        TargetForEval interface heap calls result counter bound original frame state out)
    canonical_backward_cases

theorem canonical_for_reflect {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {counter : Nat} {bound : NativeIR.Atom} {body : List Instruction}
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetForEval interface heap calls result counter bound body frame state out) :
    ∀ original, body = canonicalCode original →
      TargetForEval interface heap calls result counter bound original frame state out := by
    induction ran using TargetForEval.rec
      (motive_1 := fun instruction frame state out _ => ∀ original,
        instruction = canonicalInstruction original →
        TargetInstructionEval interface heap calls result original frame state out)
      (motive_2 := fun root remaining frame state out _ => ∀ originalRoot originalRemaining,
        root = canonicalCode originalRoot → remaining = canonicalCode originalRemaining →
        TargetRun interface heap calls result originalRoot originalRemaining frame state out)

    canonical_backward_cases


theorem canonical_instruction_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (instruction : Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetInstructionEval interface heap calls result (canonicalInstruction instruction) frame state out ↔
      TargetInstructionEval interface heap calls result instruction frame state out :=
  ⟨fun ran => canonical_instruction_reflect ran instruction rfl, canonical_instruction_forward⟩

theorem canonical_run_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (root remaining : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (canonicalCode root) (canonicalCode remaining) frame state out ↔
      TargetRun interface heap calls result root remaining frame state out :=
  ⟨fun ran => canonical_run_reflect ran root remaining rfl rfl, canonical_run_forward⟩

theorem canonical_for_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (counter : Nat) (bound : NativeIR.Atom) (body : List Instruction)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetForEval interface heap calls result counter bound (canonicalCode body) frame state out ↔
      TargetForEval interface heap calls result counter bound body frame state out :=
  ⟨fun ran => canonical_for_reflect ran body rfl, canonical_for_forward⟩

theorem canonical_run_empty_root_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (remaining : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result [] (canonicalCode remaining) frame state out ↔
      TargetRun interface heap calls result [] remaining frame state out := by
  simpa only [canonicalCode] using canonical_run_exact interface heap calls result [] remaining frame state out

theorem canonical_function_body_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World)
    (function : NativeIR.Function) (arguments : List TargetValue)
    (before : TargetState World) (out : TargetRawResult World) :
    TargetFunctionBody interface heap calls (canonicalFunction function) arguments before out ↔
      TargetFunctionBody interface heap calls function arguments before out := by
  constructor
  · intro evaluated
    cases evaluated with
    | run fresh parameters body returned =>
        exact .run fresh parameters
          (canonical_run_reflect body function.body function.body rfl rfl) returned
  · intro evaluated
    cases evaluated with
    | run fresh parameters body returned =>
        exact .run fresh parameters (canonical_run_forward body) returned

end Mettapedia.GSLT.LanguageDef.NativeOps
