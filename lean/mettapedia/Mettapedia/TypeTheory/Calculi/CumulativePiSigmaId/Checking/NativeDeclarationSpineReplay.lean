import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeConvertedIntroductionComputation

/-!
# Checked argument recovery from declaration-headed applications

The declared type is opened along the actual argument spine. Each application
recovers its supplied function certificate, computes Pi component conversion,
and casts the supplied argument to the declared domain. The result records
arguments in application order and retains an adjustment to the original
displayed type. It does not infer admission from the syntactic declaration
type: the complete source certificate and context are independently checked.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclarationSpineReplay

open Presentation StructuralTypingReplay NativeIndexedFamilies NativeParallelReceipt

/-- A syntactic declaration-spine type, not a typing or inference judgment.
Every function position must expose a Pi in its instantiated declared type. -/
def declaredType {n : Nat} : Tower.Tm n → Option (Tower.Tm n)
  | .const name => (IntrinsicRelator.rules.constantType name).map liftClosed
  | .app function argument => do
      let .pi _ body ← declaredType function | none
      return inst0 argument body
  | _ => none

def arguments {n : Nat} : Tower.Tm n → List (Tower.Tm n)
  | .app function argument => arguments function ++ [argument]
  | _ => []

/-- The instantiated domain at each original application position. -/
def declaredArguments {n : Nat} : Tower.Tm n → Option (List (Tower.Tm n × Tower.Tm n))
  | .const name => (IntrinsicRelator.rules.constantType name).map fun _ => []
  | .app function argument => do
      let previous ← declaredArguments function
      let .pi domain _ ← declaredType function | none
      return previous ++ [(argument, domain)]
  | _ => none

structure Argument (n : Nat) where
  subject : Tower.Tm n
  type : Tower.Tm n
  code : Code n

structure Result (n : Nat) where
  type : Tower.Tm n
  code : Code n
  tail : ResultTail Tower.Head NativeRelatorConversionChecking.Code n
  arguments : List (Argument n)

def applyArgument {n : Nat} (contextCode : ContextCode n)
    (function argument A : Tower.Tm n) (B : Tower.Tm (n + 1)) (displayed : Tower.Tm n)
    (functionCode argumentCode : Code n) (previous : Result n) : Option (Result n) := do
  let .pi domain body := previous.type | none
  if domain = A ∧ body = B then
    return ⟨inst0 argument body, .appElim domain body previous.code argumentCode,
      .hole, previous.arguments ++ [⟨argument, domain, argumentCode⟩]⟩
  let conversion ← previous.tail.conversion? (.refl) (.trans) previous.type
  let components ← checkedPiComponents conversion domain A body B
  let (_, functionFormation) ← resultFormation contextCode function previous.type previous.code
  let (u, _, domainFormation, _) ← functionFormation.piFormation
  let alignedArgument := Code.convert A u argumentCode domainFormation components.1.symm.code
  let (v, formation) ← resultFormation contextCode (.app function argument) displayed
    (.appElim A B functionCode argumentCode)
  return ⟨inst0 argument body, .appElim domain body previous.code alignedArgument,
    .convert (inst0 argument body) v formation
      (NativeRelatorConversionChecking.substitute (subst0 argument) components.2.code) .hole,
    previous.arguments ++ [⟨argument, domain, alignedArgument⟩]⟩

def recover {n : Nat} (contextCode : ContextCode n) (subject displayed : Tower.Tm n) :
    Code n → Option (Result n)
  | .const level formation => do
      let .const name := subject | none
      let type ← IntrinsicRelator.rules.constantType name
      return ⟨liftClosed type, .const level formation, .hole, []⟩
  | .appElim A B functionCode argumentCode => do
      let .app function argument := subject | none
      let previous ← recover contextCode function (.pi A B) functionCode
      applyArgument contextCode function argument A B displayed functionCode argumentCode previous
  | .cumul u source => do
      let .head _ := displayed | none
      let previous ← recover contextCode subject (.head u) source
      return { previous with tail := .cumul u previous.tail }
  | .convert sourceType u source formation conversion => do
      let previous ← recover contextCode subject sourceType source
      return { previous with tail := .convert sourceType u formation conversion previous.tail }
  | _ => none

structure Valid {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (result : Result n) : Prop where
  principal : check context subject result.type contextCode result.code = true
  replay : check context subject displayed contextCode (result.tail.fill result.code) = true
  view : (result.tail.fill result.code).principalView displayed =
    some ⟨result.type, result.code, result.tail⟩
  arguments_checked : ∀ entry ∈ result.arguments,
    check context entry.subject entry.type contextCode entry.code = true
  arguments_exact : result.arguments.map Argument.subject = arguments subject
  declared : declaredType subject = some result.type
  arguments_declared : declaredArguments subject =
    some (result.arguments.map fun entry => (entry.subject, entry.type))

theorem Valid.replayReplacement {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {result : Result n}
    (valid : Valid context contextCode subject displayed result)
    {replacement : Tower.Tm n} {replacementCode : Code n}
    (accepted : check context replacement result.type contextCode replacementCode = true) :
    check context replacement displayed contextCode (result.tail.fill replacementCode) = true := by
  have source := valid.replay
  simp only [check, checkJudgment, Bool.and_eq_true] at source accepted ⊢
  obtain ⟨view, computed, _, replay⟩ := Code.principalView_checked IntrinsicRelator.rules
    NativeRelatorConversionChecking.check (result.tail.fill result.code) source.2
  rw [valid.view] at computed
  cases computed
  exact ⟨accepted.1, replay replacement replacementCode accepted.2⟩

theorem Valid.conversion {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {result : Result n}
    (valid : Valid context contextCode subject displayed result)
    {domain : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (shape : result.type = .pi domain body) :
    ∃ conversion, result.tail.conversion? (.refl) (.trans) result.type = some conversion ∧
      NativeRelatorConversionChecking.check conversion result.type displayed = true := by
  have source := valid.replay
  simp only [check, checkJudgment, Bool.and_eq_true] at source
  apply Code.principal_conversion_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
    (.refl) (.trans)
    (StructuralConversionCode.Code.check_refl Tower.HeadEq NativeRelatorRootConversionCode.decode)
    (StructuralConversionCode.Code.check_trans Tower.HeadEq NativeRelatorRootConversionCode.decode)
    (result.tail.fill result.code) source.2 valid.view
  intro head conversion
  rw [shape]
  exact FormationSensitiveNativeRelatorQualification.check_pi_head_rejected conversion domain body head

theorem applyArgument_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {function argument A displayed : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {functionCode argumentCode : Code n} {previous : Result n}
    (accepted : check context (.app function argument) displayed contextCode
      (.appElim A B functionCode argumentCode) = true)
    (valid : Valid context contextCode function (.pi A B) previous)
    {domain : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (shape : previous.type = .pi domain body) :
    ∃ result, applyArgument contextCode function argument A B displayed
        functionCode argumentCode previous = some result ∧
      result.type = inst0 argument body ∧
      Valid context contextCode (.app function argument) displayed result := by
  have inputs := accepted
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have displayedEq := inputs.2.2
  subst displayed
  by_cases aligned : domain = A ∧ body = B
  · obtain ⟨rfl, rfl⟩ := aligned
    let principal := Code.appElim domain body previous.code argumentCode
    let result : Result n := ⟨inst0 argument body, principal, .hole,
      previous.arguments ++ [⟨argument, domain, argumentCode⟩]⟩
    have functionChecked := valid.principal
    rw [shape] at functionChecked
    have principalChecked : check context (.app function argument) (inst0 argument body)
        contextCode principal = true := by
      simp only [check, checkJudgment, Bool.and_eq_true] at functionChecked
      simp only [principal, check, checkJudgment, StructuralTypingReplay.check,
        Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨inputs.1, ⟨⟨functionChecked.2, inputs.2.1.2⟩, True.intro⟩⟩
    refine ⟨result, ?_, rfl, principalChecked, principalChecked, rfl, ?_, ?_, ?_, ?_⟩
    · simp [applyArgument, shape, result, principal]
    · intro entry member
      simp only [result, List.mem_append, List.mem_singleton] at member
      rcases member with prior | rfl
      · exact valid.arguments_checked entry prior
      · simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.2
    · simp only [result, List.map_append, List.map_cons, List.map_nil,
        valid.arguments_exact, arguments]
    · simp [declaredType, valid.declared, shape, result]
    · simp [declaredArguments, valid.arguments_declared, valid.declared, shape, result]
  obtain ⟨conversion, conversionComputed, converted⟩ := valid.conversion shape
  rw [shape] at converted
  let components := piComponents (⟨conversion, converted⟩ :
    NativeCompletedRootCertificate.Certificate (.pi domain body) (.pi A B))
  have componentComputed : checkedPiComponents conversion domain A body B = some components := by
    simp only [checkedPiComponents, converted, ↓reduceDIte, components]
  obtain ⟨functionLevel, functionFormation, functionComputed, _, functionFormed⟩ :=
    resultFormation_checked valid.principal
  rw [shape] at functionFormed
  have functionFormedRaw := functionFormed
  simp only [check, checkJudgment, Bool.and_eq_true] at functionFormedRaw
  obtain ⟨u, v, domainFormation, bodyFormation, formationComputed, isU, _, domainFormed, _⟩ :=
    Code.piFormation_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
      functionFormation functionFormedRaw.2
  let alignedArgument := Code.convert A u argumentCode domainFormation components.1.symm.code
  have argumentChecked : check context argument domain contextCode alignedArgument = true := by
    simp only [alignedArgument, check, checkJudgment, StructuralTypingReplay.check,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨isU, inputs.2.1.2⟩, domainFormed⟩, components.1.symm.checked⟩⟩
  let principal := Code.appElim domain body previous.code alignedArgument
  have principalChecked : check context (.app function argument) (inst0 argument body)
      contextCode principal = true := by
    have functionChecked := valid.principal
    rw [shape] at functionChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at functionChecked argumentChecked
    simp only [principal, check, checkJudgment, StructuralTypingReplay.check,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨functionChecked.2, argumentChecked.2⟩, True.intro⟩⟩
  obtain ⟨level, formation, resultComputed, isLevel, resultFormed⟩ := resultFormation_checked accepted
  let tail : ResultTail Tower.Head NativeRelatorConversionChecking.Code n :=
    .convert (inst0 argument body) level formation
      (NativeRelatorConversionChecking.substitute (subst0 argument) components.2.code) .hole
  let result : Result n := ⟨inst0 argument body, principal, tail,
    previous.arguments ++ [⟨argument, domain, alignedArgument⟩]⟩
  refine ⟨result, ?_, rfl, principalChecked, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [shape] at conversionComputed functionComputed
    simp [applyArgument, shape, aligned, conversionComputed, componentComputed,
      functionComputed, formationComputed, resultComputed, result, principal, tail, alignedArgument]
  · have principalRaw := principalChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at principalRaw resultFormed
    simp only [result, tail, ResultTail.fill, check, checkJudgment,
      StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨isLevel, principalRaw.2⟩, resultFormed.2⟩,
      NativeRelatorConversionChecking.check_substitute (subst0 argument) components.2.code
        components.2.checked⟩⟩
  · rfl
  · intro entry member
    simp only [result, List.mem_append, List.mem_singleton] at member
    rcases member with prior | rfl
    · exact valid.arguments_checked entry prior
    · exact argumentChecked
  · simp only [result, List.map_append, List.map_cons, List.map_nil,
      valid.arguments_exact, arguments]
  · simp [declaredType, valid.declared, shape, result]
  · simp [declaredArguments, valid.arguments_declared, valid.declared, shape, result]

#print axioms applyArgument_checked

/-- Every admitted spine whose instantiated declaration exposes the needed
Pi constructors yields checked arguments and a checked canonical result.
The algorithm consumes the supplied evidence, including internal conversions. -/
theorem recover_checked {n : Nat} (code : Code n) :
    ∀ (context : Tower.Ctx n) (contextCode : ContextCode n)
      (subject displayed expected : Tower.Tm n),
      check context subject displayed contextCode code = true →
      declaredType subject = some expected →
      ∃ result, recover contextCode subject displayed code = some result ∧
        result.type = expected ∧ Valid context contextCode subject displayed result := by
  induction code with
  | const level formation _ =>
      intro context contextCode subject displayed expected accepted predicted
      cases subject <;>
        simp only [check, checkJudgment, StructuralTypingReplay.check,
          Bool.and_eq_true, Bool.false_eq_true, and_false] at accepted
      rename_i name
      cases known : IntrinsicRelator.rules.constantType name with
      | none => simp [known] at accepted
      | some declared =>
          simp only [known, Bool.and_eq_true, decide_eq_true_eq] at accepted
          simp [declaredType, known] at predicted
          subst expected
          have displayedEq := accepted.2.2
          subst displayed
          have original : check context (.const name) (liftClosed declared) contextCode
              (.const level formation) = true := by
            simpa only [check, checkJudgment, StructuralTypingReplay.check, known,
              Bool.and_eq_true, decide_eq_true_eq] using accepted
          refine ⟨⟨liftClosed declared, .const level formation, .hole, []⟩,
            ?_, rfl, original, original, rfl, ?_, rfl, ?_, ?_⟩
          · simp [recover, known]
          · intro entry member
            cases member
          · simp [declaredType, known]
          · simp [declaredArguments, known]
  | appElim A B functionCode argumentCode ih _ =>
      intro context contextCode subject displayed expected accepted predicted
      have inputs := accepted
      cases subject <;>
        simp only [check, checkJudgment, StructuralTypingReplay.check,
          Bool.and_eq_true, Bool.false_eq_true, and_false] at inputs
      rename_i function argument
      cases functionType : declaredType function with
      | none => simp [declaredType, functionType] at predicted
      | some actual =>
          cases actual <;> simp [declaredType, functionType] at predicted
          rename_i domain body
          subst expected
          have functionChecked : check context function (.pi A B) contextCode functionCode = true := by
            simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.1
          obtain ⟨previous, recovered, shape, valid⟩ :=
            ih context contextCode function (.pi A B) (.pi domain body) functionChecked functionType
          obtain ⟨result, computed, resultType, resultValid⟩ := applyArgument_checked accepted valid shape
          refine ⟨result, ?_, resultType, resultValid⟩
          simp [recover, recovered, computed]
  | cumul u source ih =>
      intro context contextCode subject displayed expected accepted predicted
      have inputs := accepted
      cases displayed <;>
        simp only [check, checkJudgment, StructuralTypingReplay.check,
          Bool.and_eq_true, Bool.false_eq_true, and_false] at inputs
      rename_i targetLevel
      have sourceChecked : check context subject (.head u) contextCode source = true := by
        simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1
      obtain ⟨previous, recovered, same, valid⟩ :=
        ih context contextCode subject (.head u) expected sourceChecked predicted
      refine ⟨{ previous with tail := .cumul u previous.tail }, ?_, same,
        valid.principal, ?_, ?_, valid.arguments_checked, valid.arguments_exact,
        valid.declared, valid.arguments_declared⟩
      · simp [recover, recovered]
      · have replay := valid.replay
        simp only [check, checkJudgment, Bool.and_eq_true] at replay
        simpa only [ResultTail.fill, check, checkJudgment, StructuralTypingReplay.check,
          Bool.and_eq_true] using And.intro inputs.1 (And.intro replay.2 inputs.2.2)
      · simp only [ResultTail.fill, Code.principalView, valid.view, Option.map_some]
  | convert sourceType level source formation conversion ih _ =>
      intro context contextCode subject displayed expected accepted predicted
      have inputs := accepted
      simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true] at inputs
      have sourceChecked : check context subject sourceType contextCode source = true := by
        simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.1.2
      obtain ⟨previous, recovered, same, valid⟩ :=
        ih context contextCode subject sourceType expected sourceChecked predicted
      refine ⟨{ previous with tail := .convert sourceType level formation conversion previous.tail },
        ?_, same, valid.principal, ?_, ?_, valid.arguments_checked, valid.arguments_exact,
        valid.declared, valid.arguments_declared⟩
      · simp [recover, recovered]
      · have replay := valid.replay
        simp only [check, checkJudgment, Bool.and_eq_true] at replay
        simp only [ResultTail.fill, check, checkJudgment, StructuralTypingReplay.check,
          Bool.and_eq_true]
        exact ⟨inputs.1, ⟨⟨⟨inputs.2.1.1.1, replay.2⟩, inputs.2.1.2⟩, inputs.2.2⟩⟩
      · simp only [ResultTail.fill, Code.principalView, valid.view, Option.map_some]
  | _ =>
      intro context contextCode subject displayed expected accepted predicted
      cases subject <;> simp_all only [declaredType, check, checkJudgment,
        StructuralTypingReplay.check, Bool.and_eq_true, Bool.false_eq_true,
        and_false, reduceCtorEq]

#print axioms recover_checked

/-- Source admission and exposure of the declaration's Pi spine are separate
checks. Neither successful lookup nor raw extraction establishes typing. -/
def checkedRecover {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) : Option (Result n) :=
  if check context subject displayed contextCode code then
    (declaredType subject).bind fun _ => recover contextCode subject displayed code
  else none

theorem checkedRecover_domain {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) :
    (checkedRecover context contextCode subject displayed code).isSome =
      (check context subject displayed contextCode code && (declaredType subject).isSome) := by
  unfold checkedRecover
  split
  · rename_i accepted
    cases predicted : declaredType subject with
    | none => simp
    | some expected =>
        obtain ⟨result, computed, _, _⟩ :=
          recover_checked code context contextCode subject displayed expected accepted predicted
        simp [computed, accepted]
  · rename_i rejected
    simp [Bool.eq_false_iff.mpr rejected]

theorem checkedRecover_sound {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {code : Code n} {result : Result n}
    (computed : checkedRecover context contextCode subject displayed code = some result) :
    check context subject displayed contextCode code = true ∧
      declaredType subject = some result.type ∧
      Valid context contextCode subject displayed result := by
  unfold checkedRecover at computed
  split at computed
  · rename_i accepted
    cases predicted : declaredType subject with
    | none => simp [predicted] at computed
    | some expected =>
        obtain ⟨actual, recovered, same, valid⟩ :=
          recover_checked code context contextCode subject displayed expected accepted predicted
        simp only [predicted, Option.bind_some, recovered, Option.some.injEq] at computed
        subst result
        exact ⟨accepted, congrArg some same.symm, valid⟩
  · contradiction

#print axioms checkedRecover_domain
#print axioms checkedRecover_sound

/-- Select an original argument by its declared position, retaining its
computed certificate and the instantiated domain at that position. -/
theorem Valid.argumentAt {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed : Tower.Tm n} {result : Result n}
    (valid : Valid context contextCode subject displayed result)
    (position : Nat) {argument type : Tower.Tm n}
    (selected : (declaredArguments subject).bind (fun entries => entries[position]?) =
      some (argument, type)) :
    ∃ entry, result.arguments[position]? = some entry ∧ entry.subject = argument ∧
      entry.type = type ∧ check context argument type contextCode entry.code = true := by
  rw [valid.arguments_declared] at selected
  simp only [Option.bind_some, List.getElem?_map] at selected
  obtain ⟨entry, found, same⟩ := Option.map_eq_some_iff.mp selected
  obtain ⟨subjectEq, typeEq⟩ := Prod.mk.inj same
  refine ⟨entry, found, subjectEq, typeEq, ?_⟩
  have checked := valid.arguments_checked entry (List.mem_of_getElem? found)
  simpa only [subjectEq, typeEq] using checked

def returnArgument {n : Nat} (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) (position : Nat) : Option (Code n) := do
  let result ← recover contextCode subject displayed code
  let entry ← result.arguments[position]?
  return result.tail.fill entry.code

theorem returnArgument_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {subject displayed expected argument : Tower.Tm n} {code : Code n} (position : Nat)
    (accepted : check context subject displayed contextCode code = true)
    (predicted : declaredType subject = some expected)
    (selected : (declaredArguments subject).bind (fun entries => entries[position]?) =
      some (argument, expected)) :
    ∃ output, returnArgument contextCode subject displayed code position = some output ∧
      check context argument displayed contextCode output = true := by
  obtain ⟨result, computed, same, valid⟩ :=
    recover_checked code context contextCode subject displayed expected accepted predicted
  obtain ⟨entry, found, _, _, entryChecked⟩ := valid.argumentAt position selected
  refine ⟨result.tail.fill entry.code, ?_, ?_⟩
  · simp [returnArgument, computed, found]
  · apply valid.replayReplacement
    simpa only [same] using entryChecked

#print axioms Valid.argumentAt
#print axioms returnArgument_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclarationSpineReplay
