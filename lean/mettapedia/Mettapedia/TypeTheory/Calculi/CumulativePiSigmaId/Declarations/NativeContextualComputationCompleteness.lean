import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeContextualComputationReplay

/-!
# Completeness laws for the native contextual certificate driver

The laws concern actual outputs of the driver, not just the existence of a
typing derivation after reduction. Declared roots are total on admitted
instances. Contextual closure lemmas consume the recursive premise's execution
property and earn the enclosing execution at its unchanged displayed type.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ContextualComputation

open Presentation StructuralTypingReplay NativeIndexedFamilies

theorem execute_root_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    (root : NativeRelatorRootConversionCode.Code n)
    (decoded : NativeRelatorRootConversionCode.decode root = some (source, target))
    (accepted : check context source displayed contextCode code = true) :
    ∃ output, execute (.root root) contextCode displayed code = some output ∧
      check context target displayed contextCode output = true := by
  obtain ⟨result, computed, termEq, _, checked⟩ := DeclaredRootExecution.execute_complete root decoded accepted
  refine ⟨result.code, ?_, ?_⟩
  · simp only [execute, computed, Option.map_some]
  · simpa only [termEq] using checked

theorem execute_appArgument_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next function displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.app function old) displayed contextCode code = true) :
    ∃ output, execute (.congAppArg function nested) contextCode displayed code = some output ∧
      check context (.app function next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i A B functionCode argumentCode
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have typeEq := inputs.2.2
  subst type
  have childChecked : check context old A contextCode argumentCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.2
  obtain ⟨newArgument, argumentComputed, argumentChecked⟩ := childComplete A argumentCode childChecked
  obtain ⟨output, computed, outputChecked⟩ := DependentCongruence.appArgument_checked checked argumentChecked
    (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)
  refine ⟨output, ?_, outputChecked⟩
  simp only [decoded, argumentComputed, bind, Option.bind, computed]

/-- Any of the five declared native rules can execute inside an accepted
dependent application, including through arbitrary source result conversions. -/
theorem declared_root_in_argument_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next function displayed : Tower.Tm n} {code : Code n}
    (root : NativeRelatorRootConversionCode.Code n)
    (decoded : NativeRelatorRootConversionCode.decode root = some (old, next))
    (accepted : check context (.app function old) displayed contextCode code = true) :
    ∃ output, execute (.congAppArg function (.root root)) contextCode displayed code = some output ∧
      check context (.app function next) displayed contextCode output = true :=
  execute_appArgument_complete (.root root) decoded
    (fun _ _ childChecked => execute_root_complete root decoded childChecked) accepted


theorem execute_piDomain_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm n} {body : Tower.Tm (n + 1)} {displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.pi old body) displayed contextCode code = true) :
    ∃ output, execute (.congPiDom nested body) contextCode displayed code = some output ∧
      check context (.pi next body) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i u v domain bodyCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  change check context (.pi old body) (.head w) contextCode (.piForm u v domain bodyCode) = true at checked
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq] at inputs
  have childChecked : check context old (.head u) contextCode domain = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.2
  obtain ⟨newDomain, domainComputed, domainChecked⟩ := childComplete (.head u) domain childChecked
  refine ⟨DependentCongruence.piDomain next body u v domain newDomain bodyCode (.single nested), ?_, ?_⟩
  · simp only [decoded, domainComputed, bind, Option.bind, pure]
  · exact DependentCongruence.piDomain_checked checked domainChecked
      (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)

theorem execute_sigmaDomain_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm n} {body : Tower.Tm (n + 1)} {displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.sigma old body) displayed contextCode code = true) :
    ∃ output, execute (.congSigmaDom nested body) contextCode displayed code = some output ∧
      check context (.sigma next body) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i u v domain bodyCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  change check context (.sigma old body) (.head w) contextCode (.sigmaForm u v domain bodyCode) = true at checked
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq] at inputs
  have childChecked : check context old (.head u) contextCode domain = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.2
  obtain ⟨newDomain, domainComputed, domainChecked⟩ := childComplete (.head u) domain childChecked
  refine ⟨DependentCongruence.sigmaDomain next body u v domain newDomain bodyCode (.single nested), ?_, ?_⟩
  · simp only [decoded, domainComputed, bind, Option.bind, pure]
  · exact DependentCongruence.sigmaDomain_checked checked domainChecked
      (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)

theorem execute_pairFirst_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next second displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.pair old second) displayed contextCode code = true) :
    ∃ output, execute (.congPairFst nested second) contextCode displayed code = some output ∧
      check context (.pair next second) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i level formation firstCode secondCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i A B
  change check context (.pair old second) (.sigma A B) contextCode
    (.pairIntro level formation firstCode secondCode) = true at checked
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq] at inputs
  have childChecked : check context old A contextCode firstCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.2
  obtain ⟨newFirst, firstComputed, firstChecked⟩ := childComplete A firstCode childChecked
  obtain ⟨output, computed, outputChecked⟩ := DependentCongruence.pairFirst_checked checked firstChecked
    (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)
  refine ⟨output, ?_, outputChecked⟩
  simp only [decoded, firstComputed, bind, Option.bind, computed]

theorem execute_sndArgument_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.snd old) displayed contextCode code = true) :
    ∃ output, execute (.congSnd nested) contextCode displayed code = some output ∧
      check context (.snd next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i A B pairCode
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have typeEq := inputs.2.2
  subst type
  have childChecked : check context old (.sigma A B) contextCode pairCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1
  obtain ⟨newPair, pairComputed, pairChecked⟩ := childComplete (.sigma A B) pairCode childChecked
  obtain ⟨output, computed, outputChecked⟩ := DependentCongruence.sndArgument_checked checked pairChecked
    (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)
  refine ⟨output, ?_, outputChecked⟩
  simp only [decoded, pairComputed, bind, Option.bind, computed]

theorem execute_reflArgument_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.refl old) displayed contextCode code = true) :
    ∃ output, execute (.congRefl nested) contextCode displayed code = some output ∧
      check context (.refl next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i A termCode
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have typeEq := inputs.2.2
  subst type
  have childChecked : check context old A contextCode termCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1
  obtain ⟨newTerm, termComputed, termChecked⟩ := childComplete A termCode childChecked
  obtain ⟨output, computed, outputChecked⟩ := DependentCongruence.reflArgument_checked checked termChecked
    (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)
  refine ⟨output, ?_, outputChecked⟩
  simp only [decoded, termComputed, bind, Option.bind, computed]


theorem execute_appFunction_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next argument displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.app old argument) displayed contextCode code = true) :
    ∃ output, execute (.congAppFun nested argument) contextCode displayed code = some output ∧
      check context (.app next argument) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i A B functionCode argumentCode
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have childChecked : check context old (.pi A B) contextCode functionCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.1
  obtain ⟨newChild, computed, newChecked⟩ := childComplete (.pi A B) functionCode childChecked
  refine ⟨.appElim A B newChild argumentCode, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨newInputs.2, inputs.2.1.2⟩, inputs.2.2⟩⟩

theorem execute_fstArgument_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next  displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.fst old) displayed contextCode code = true) :
    ∃ output, execute (.congFst nested) contextCode displayed code = some output ∧
      check context (.fst next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i B pairCode
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true] at inputs
  have childChecked : check context old (.sigma type B) contextCode pairCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2
  obtain ⟨newChild, computed, newChecked⟩ := childComplete (.sigma type B) pairCode childChecked
  refine ⟨.fstElim B newChild, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true]
    exact ⟨inputs.1, newInputs.2⟩

theorem execute_pairSecond_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next first displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.pair first old) displayed contextCode code = true) :
    ∃ output, execute (.congPairSnd first nested) contextCode displayed code = some output ∧
      check context (.pair first next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i level formation firstCode secondCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i A B
  change check context (.pair first old) (.sigma A B) contextCode (.pairIntro level formation firstCode secondCode) = true at checked
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have childChecked : check context old (inst0 first B) contextCode secondCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.2
  obtain ⟨newChild, computed, newChecked⟩ := childComplete (inst0 first B) secondCode childChecked
  refine ⟨.pairIntro level formation firstCode newChild, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨inputs.2.1.1.1, inputs.2.1.1.2⟩, inputs.2.1.2⟩, newInputs.2⟩⟩

theorem execute_identityLeft_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next A right displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.id A old right) displayed contextCode code = true) :
    ∃ output, execute (.congIdLeft A nested right) contextCode displayed code = some output ∧
      check context (.id A next right) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i level formation leftCode rightCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  change check context (.id A old right) (.head w) contextCode (.idForm level formation leftCode rightCode) = true at checked
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have childChecked : check context old (A) contextCode leftCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.1.2
  obtain ⟨newChild, computed, newChecked⟩ := childComplete (A) leftCode childChecked
  refine ⟨.idForm level formation newChild rightCode, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨⟨inputs.2.1.1.1.1, inputs.2.1.1.1.2⟩, newInputs.2⟩, inputs.2.1.2⟩, inputs.2.2⟩⟩

theorem execute_identityRight_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next A left displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.id A left old) displayed contextCode code = true) :
    ∃ output, execute (.congIdRight A left nested) contextCode displayed code = some output ∧
      check context (.id A left next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i level formation leftCode rightCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  change check context (.id A left old) (.head w) contextCode (.idForm level formation leftCode rightCode) = true at checked
  have inputs := checked
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at inputs
  have childChecked : check context old (A) contextCode rightCode = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.2
  obtain ⟨newChild, computed, newChecked⟩ := childComplete (A) rightCode childChecked
  refine ⟨.idForm level formation leftCode newChild, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨⟨inputs.2.1.1.1.1, inputs.2.1.1.1.2⟩, inputs.2.1.1.2⟩, newInputs.2⟩, inputs.2.2⟩⟩


theorem execute_identityType_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next left right displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep nested = some (old, next))
    (childComplete : ∀ (type : Tower.Tm n) (child : Code n),
      check context old type contextCode child = true →
      ∃ output, execute nested contextCode type child = some output ∧
        check context next type contextCode output = true)
    (accepted : check context (.id old left right) displayed contextCode code = true) :
    ∃ output, execute (.congIdTy nested left right) contextCode displayed code = some output ∧
      check context (.id next left right) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i level formation leftCode rightCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  have inputs := checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at inputs
  have typeEq := inputs.2.2
  subst w
  change check context (.id old left right) (.head level) contextCode
    (.idForm level formation leftCode rightCode) = true at checked
  have childChecked : check context old (.head level) contextCode formation = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 inputs.2.1.1.1.2
  obtain ⟨newFormation, computed, newChecked⟩ := childComplete (.head level) formation childChecked
  refine ⟨DependentCongruence.identityType old level newFormation leftCode rightCode (.single nested), ?_, ?_⟩
  · simp only [decoded, computed, bind, Option.bind, pure]
  · exact DependentCongruence.identityType_checked checked newChecked
      (show NativeRelatorConversionChecking.check (.single nested) old next = true from decide_eq_true decoded)

theorem execute_lambda_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm (n + 1)} {displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode (n + 1))
    (childComplete : ∀ (childContext : Tower.Ctx (n + 1)) (childContextCode : ContextCode (n + 1))
      (type : Tower.Tm (n + 1)) (child : Code (n + 1)),
      check childContext old type childContextCode child = true →
      ∃ output, execute nested childContextCode type child = some output ∧
        check childContext next type childContextCode output = true)
    (accepted : check context (.lam old) displayed contextCode code = true) :
    ∃ output, execute (.congLam nested) contextCode displayed code = some output ∧
      check context (.lam next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i level formation bodyCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i A B
  have inputs := checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at inputs
  obtain ⟨u, v, domain, bodyFormation, formationComputed, isU, _, domainChecked, _⟩ :=
    Code.piFormation_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
      formation inputs.2.1.2
  have childChecked : check (.snoc context A) old B (.snoc contextCode u domain) bodyCode = true := by
    simp only [check, checkJudgment, checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨inputs.1, isU⟩, domainChecked⟩, inputs.2.2⟩
  obtain ⟨newBody, computed, newChecked⟩ := childComplete _ _ B bodyCode childChecked
  refine ⟨.lamIntro level formation newBody, ?_, ?_⟩
  · simp only [formationComputed, computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨inputs.2.1.1, inputs.2.1.2⟩, newInputs.2⟩⟩

theorem execute_piCodomain_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm (n + 1)} {A displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode (n + 1))
    (childComplete : ∀ (childContext : Tower.Ctx (n + 1)) (childContextCode : ContextCode (n + 1))
      (type : Tower.Tm (n + 1)) (child : Code (n + 1)),
      check childContext old type childContextCode child = true →
      ∃ output, execute nested childContextCode type child = some output ∧
        check childContext next type childContextCode output = true)
    (accepted : check context (.pi A old) displayed contextCode code = true) :
    ∃ output, execute (.congPiCod A nested) contextCode displayed code = some output ∧
      check context (.pi A next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i u v domain bodyCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  have inputs := checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at inputs
  have childChecked : check (.snoc context A) old (.head v) (.snoc contextCode u domain) bodyCode = true := by
    simp only [check, checkJudgment, checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨inputs.1, inputs.2.1.1.1.1⟩, inputs.2.1.2⟩, inputs.2.2⟩
  obtain ⟨newBody, computed, newChecked⟩ := childComplete _ _ (.head v) bodyCode childChecked
  refine ⟨.piForm u v domain newBody, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨⟨inputs.2.1.1.1.1, inputs.2.1.1.1.2⟩, inputs.2.1.1.2⟩,
      inputs.2.1.2⟩, newInputs.2⟩⟩

theorem execute_sigmaCodomain_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {old next : Tower.Tm (n + 1)} {A displayed : Tower.Tm n} {code : Code n}
    (nested : NativeRelatorConversionChecking.StepCode (n + 1))
    (childComplete : ∀ (childContext : Tower.Ctx (n + 1)) (childContextCode : ContextCode (n + 1))
      (type : Tower.Tm (n + 1)) (child : Code (n + 1)),
      check childContext old type childContextCode child = true →
      ∃ output, execute nested childContextCode type child = some output ∧
        check childContext next type childContextCode output = true)
    (accepted : check context (.sigma A old) displayed contextCode code = true) :
    ∃ output, execute (.congSigmaCod A nested) contextCode displayed code = some output ∧
      check context (.sigma A next) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  rename_i u v domain bodyCode
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i w
  have inputs := checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at inputs
  have childChecked : check (.snoc context A) old (.head v) (.snoc contextCode u domain) bodyCode = true := by
    simp only [check, checkJudgment, checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨inputs.1, inputs.2.1.1.1.1⟩, inputs.2.1.2⟩, inputs.2.2⟩
  obtain ⟨newBody, computed, newChecked⟩ := childComplete _ _ (.head v) bodyCode childChecked
  refine ⟨.sigmaForm u v domain newBody, ?_, ?_⟩
  · simp only [computed, bind, Option.bind, pure]
  · have newInputs := newChecked
    simp only [check, checkJudgment, Bool.and_eq_true] at newInputs
    simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, ⟨⟨⟨⟨inputs.2.1.1.1.1, inputs.2.1.1.1.2⟩, inputs.2.1.1.2⟩,
      inputs.2.1.2⟩, newInputs.2⟩⟩


private def introductionTarget {n : Nat} : Tower.Tm n → Option (Tower.Tm n)
  | .app (.lam body) argument => some (inst0 argument body)
  | .fst (.pair first _) => some first
  | .snd (.pair _ second) => some second
  | _ => none

private theorem direct_target {n : Nat} {contextCode : ContextCode n}
    {source type : Tower.Tm n} {code : Code n} {result : PrincipalComputation.Result n}
    (computed : PrincipalComputation.direct contextCode source type code = some result) :
    introductionTarget source = some result.term := by
  unfold PrincipalComputation.direct at computed
  split at computed
  all_goals first
    | cases computed; rfl
    | obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp computed; rfl
    | contradiction

private theorem introduction_shape {n : Nat} {context : Tower.Ctx n}
    {source target type : Tower.Tm n} {code : Code n}
    (selected : introductionTarget source = some target)
    (principal : code.isPrincipal = true)
    (checked : StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
      context source type code = true) :
    PrincipalComputation.directShape source code = true := by
  unfold introductionTarget at selected
  split at selected
  all_goals try contradiction
  all_goals cases code <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [StructuralTypingReplay.check] at checked }
  all_goals rfl

private theorem introduction_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    (selected : introductionTarget source = some target)
    (accepted : check context source displayed contextCode code = true) :
    ∃ result, PrincipalComputation.execute contextCode source displayed code = some result ∧
      result.term = target ∧ check context target displayed contextCode result.code = true := by
  have inputs := accepted
  simp only [check, checkJudgment, Bool.and_eq_true] at inputs
  obtain ⟨view, computed, checked, replay⟩ :=
    Code.principalView_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check code inputs.2
  have shape := introduction_shape selected (Code.principalView_reconstruct code computed).2 checked
  have inner : check context source view.type contextCode view.code = true := by
    simpa only [check, checkJudgment, Bool.and_eq_true] using And.intro inputs.1 checked
  have domain := PrincipalComputation.direct_domain inner
  cases executed : PrincipalComputation.direct contextCode source view.type view.code with
  | none => simp [executed, shape] at domain
  | some result =>
      have termEq : result.term = target := Option.some.inj ((direct_target executed).symm.trans selected)
      have outputChecked := (PrincipalComputation.direct_checked inner executed).1
      refine ⟨{result with code := view.tail.fill result.code}, ?_, termEq, ?_⟩
      · simp only [PrincipalComputation.execute, computed, executed, Option.bind_some, Option.map_some]
      · simp only [check, checkJudgment, Bool.and_eq_true] at outputChecked ⊢
        exact ⟨inputs.1, replay target result.code (by simpa only [termEq] using outputChecked.2)⟩

private theorem successor_heads_equal {left right : Tower.Head} (equal : Tower.HeadEq left right) :
    Tower.HeadEq (TowerDecisions.headTarget right) (TowerDecisions.headTarget left) := by
  cases left <;> cases right <;> simp only [LevelTower.HeadEq, TowerDecisions.headTarget] at equal ⊢
  · simp
  · intro valuation
    exact congrArg Nat.succ (equal valuation).symm

theorem execute_head_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {left right : Tower.Head} {displayed : Tower.Tm n} {code : Code n}
    (equal : Tower.HeadEq left right)
    (accepted : check context (.head left) displayed contextCode code = true) :
    ∃ output, execute (.head left right) contextCode displayed code = some output ∧
      check context (.head right) displayed contextCode output = true := by
  apply atPrincipal_checked _ accepted
  intro type principal isPrincipal checked
  cases principal <;> simp only [Code.isPrincipal, Bool.false_eq_true] at isPrincipal
  all_goals try { simp [check, checkJudgment, StructuralTypingReplay.check] at checked }
  cases type <;> simp only [check, checkJudgment, StructuralTypingReplay.check,
    Bool.and_false, Bool.false_eq_true] at checked
  rename_i level
  have inputs := checked
  simp only [Bool.and_eq_true, decide_eq_true_eq] at inputs
  have typeEq := (TowerDecisions.headTyping_iff left level).mp inputs.2
  subst level
  apply DependentCongruence.restoreResult_checked
    (show check context (.head left) (.head (TowerDecisions.headTarget left)) contextCode .headType = true from checked)
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨inputs.1, (TowerDecisions.headTyping_iff right _).mpr rfl⟩
  · have converted := successor_heads_equal equal
    simp [NativeRelatorConversionChecking.check, StructuralConversionCode.Code.check,
      StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode, converted]



/-- Every selected contextual step executes on every accepted source, at its
original displayed dependent type. This is totality on supplied finite step
evidence, not normalization or discovery of a step. -/
theorem execute_complete {n : Nat} (step : NativeRelatorConversionChecking.StepCode n) :
    ∀ {context : Tower.Ctx n} {contextCode : ContextCode n}
      {source target displayed : Tower.Tm n} {code : Code n},
      decodeStep step = some (source, target) →
      check context source displayed contextCode code = true →
      ∃ output, execute step contextCode displayed code = some output ∧
        check context target displayed contextCode output = true := by
  induction step with
  | betaPi body argument =>
      intro context contextCode source target displayed code decoded accepted
      cases Option.some.inj decoded
      obtain ⟨result, computed, termEq, checked⟩ := introduction_complete rfl accepted
      refine ⟨result.code, ?_, checked⟩
      simp only [execute, computed, Option.map_some]
  | betaSigmaFst first second =>
      intro context contextCode source target displayed code decoded accepted
      cases Option.some.inj decoded
      obtain ⟨result, computed, termEq, checked⟩ := introduction_complete rfl accepted
      refine ⟨result.code, ?_, checked⟩
      simp only [execute, computed, Option.map_some]
  | betaSigmaSnd first second =>
      intro context contextCode source target displayed code decoded accepted
      cases Option.some.inj decoded
      obtain ⟨result, computed, termEq, checked⟩ := introduction_complete rfl accepted
      refine ⟨result.code, ?_, checked⟩
      simp only [execute, computed, Option.map_some]
  | root root =>
      intro context contextCode source target displayed code decoded accepted
      exact execute_root_complete root decoded accepted
  | head left right =>
      intro context contextCode source target displayed code decoded accepted
      change (if Tower.HeadEq left right then some (.head left, .head right) else none) =
        some (source, target) at decoded
      split at decoded
      · rename_i equal
        cases Option.some.inj decoded
        exact execute_head_complete equal accepted
      · contradiction
  | congPiDom nested body ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (fun term => .pi term body) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_piDomain_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congSigmaDom nested body ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (fun term => .sigma term body) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_sigmaDomain_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congPiCod A nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.pi A) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_piCodomain_complete nested
            (fun _ _ _ _ childChecked => ih childDecoded childChecked) accepted
  | congSigmaCod A nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.sigma A) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_sigmaCodomain_complete nested
            (fun _ _ _ _ childChecked => ih childDecoded childChecked) accepted
  | congLam nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.lam) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_lambda_complete nested
            (fun _ _ _ _ childChecked => ih childDecoded childChecked) accepted
  | congAppFun nested argument ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (fun term => .app term argument) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_appFunction_complete nested
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congAppArg function nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.app function) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_appArgument_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congPairFst nested second ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (fun term => .pair term second) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_pairFirst_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congPairSnd first nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.pair first) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_pairSecond_complete nested
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congFst nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.fst) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_fstArgument_complete nested
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congSnd nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.snd) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_sndArgument_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congRefl nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.refl) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_reflArgument_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congIdTy nested left right ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (fun term => .id term left right) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_identityType_complete nested childDecoded
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congIdLeft A nested right ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (fun term => .id A term right) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_identityLeft_complete nested
            (fun _ _ childChecked => ih childDecoded childChecked) accepted
  | congIdRight A left nested ih =>
      intro context contextCode source target displayed code decoded accepted
      change StructuralConversionCode.mapEndpoints (.id A left) (decodeStep nested) =
        some (source, target) at decoded
      cases childDecoded : decodeStep nested with
      | none => simp [childDecoded, StructuralConversionCode.mapEndpoints] at decoded
      | some pair =>
          obtain ⟨old, next⟩ := pair
          simp only [childDecoded, StructuralConversionCode.mapEndpoints, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          exact execute_identityRight_complete nested
            (fun _ _ childChecked => ih childDecoded childChecked) accepted


theorem checkedExecute_complete {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target displayed : Tower.Tm n} {code : Code n}
    (step : NativeRelatorConversionChecking.StepCode n)
    (decoded : decodeStep step = some (source, target))
    (accepted : check context source displayed contextCode code = true) :
    ∃ result, checkedExecute context contextCode source displayed code step = some result ∧
      result.term = target ∧ result.step = step := by
  obtain ⟨output, computed, checked⟩ := execute_complete step decoded accepted
  refine ⟨⟨target, output, step⟩, ?_, rfl, rfl⟩
  simp only [checkedExecute, decoded, accepted, computed, checked, bind, Option.bind, pure,
    and_self, ↓reduceIte]

/-- The result replay gate introduces no additional rejection on a valid
selected step and an admitted matching source. Invalid decoders also fail. -/
theorem checkedExecute_domain {n : Nat} (context : Tower.Ctx n) (contextCode : ContextCode n)
    (subject displayed : Tower.Tm n) (code : Code n) (step : NativeRelatorConversionChecking.StepCode n) :
    (checkedExecute context contextCode subject displayed code step).isSome =
      ((decodeStep step).map fun pair =>
        decide (pair.1 = subject) && check context subject displayed contextCode code).getD false := by
  cases decoded : decodeStep step with
  | none => simp [checkedExecute, decoded]
  | some pair =>
      obtain ⟨source, target⟩ := pair
      simp only [checkedExecute, decoded, bind, Option.bind, Option.map_some, Option.getD_some]
      split
      · rename_i admitted
        obtain ⟨rfl, accepted⟩ := admitted
        obtain ⟨output, computed, checked⟩ := execute_complete step decoded accepted
        simp [computed, checked, accepted]
      · rename_i rejected
        cases admission : decide (source = subject) && check context subject displayed contextCode code
        · rfl
        · have admitted : source = subject ∧ check context subject displayed contextCode code = true := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using admission
          exact (rejected admitted).elim

theorem checkedExecute_reindex {context destination : NativeCheckedSubstitution.Context}
    (source : NativeCheckedSubstitution.JudgmentReceipt context)
    (morphism : NativeCheckedSubstitution.Hom destination context)
    (step : NativeRelatorConversionChecking.StepCode context.arity)
    (result : PrincipalComputation.Result context.arity)
    (computed : checkedExecute context.raw context.code source.subject source.type source.code step = some result) :
    ∃ (output : PrincipalComputation.Result destination.arity)
      (outputComputed : checkedExecute destination.raw destination.code
        (source.reindex morphism).subject (source.reindex morphism).type (source.reindex morphism).code
        (StructuralConversionCode.StepCode.substitute NativeRelatorRootConversionCode.substitute
          morphism.substitution step) = some output),
      output.term = subst morphism.substitution result.term ∧
      output.step = StructuralConversionCode.StepCode.substitute NativeRelatorRootConversionCode.substitute
        morphism.substitution step ∧
      (resultReceipt (source.reindex morphism) _ output outputComputed).observe =
        ((resultReceipt source step result computed).reindex morphism).observe := by
  have decoded : decodeStep step = some (source.subject, result.term) :=
    of_decide_eq_true (checkedExecute_sound computed).2.2.2
  have mappedDecoded : decodeStep (StructuralConversionCode.StepCode.substitute
      NativeRelatorRootConversionCode.substitute morphism.substitution step) =
      some ((source.reindex morphism).subject, subst morphism.substitution result.term) := by
    rw [decodeStep, StructuralConversionCode.StepCode.decode_substitute
      NativeRelatorRootConversionCode.substitute Tower.HeadEq NativeRelatorRootConversionCode.decode
      NativeRelatorRootConversionCode.decode_substitute]
    change StructuralConversionCode.mapEndpoints (subst morphism.substitution) (decodeStep step) = _
    rw [decoded]
    rfl
  obtain ⟨output, outputComputed, termEq, stepEq⟩ := checkedExecute_complete _ mappedDecoded
    (source.reindex morphism).accepted
  refine ⟨output, outputComputed, termEq, stepEq, ?_⟩
  apply (NativeCheckedSubstitution.JudgmentReceipt.observe_eq_iff _ _).mpr
  change Conv IntrinsicRelator.rules.headEq (subst morphism.substitution source.type)
      (subst morphism.substitution source.type) IntrinsicRelator.rules.computation ∧
    Conv IntrinsicRelator.rules.headEq output.term (subst morphism.substitution result.term)
      IntrinsicRelator.rules.computation
  rw [termEq]
  exact ⟨.refl _, .refl _⟩


#print axioms checkedExecute_complete
#print axioms checkedExecute_domain
#print axioms checkedExecute_reindex
#print axioms execute_complete
#print axioms execute_head_complete
#print axioms execute_identityType_complete
#print axioms execute_lambda_complete
#print axioms execute_piCodomain_complete
#print axioms execute_sigmaCodomain_complete
#print axioms execute_appFunction_complete
#print axioms execute_fstArgument_complete
#print axioms execute_pairSecond_complete
#print axioms execute_identityLeft_complete
#print axioms execute_identityRight_complete
#print axioms execute_pairFirst_complete
#print axioms execute_sndArgument_complete
#print axioms execute_reflArgument_complete
#print axioms execute_piDomain_complete
#print axioms execute_sigmaDomain_complete
#print axioms execute_root_complete
#print axioms execute_appArgument_complete
#print axioms declared_root_in_argument_complete

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.ContextualComputation
