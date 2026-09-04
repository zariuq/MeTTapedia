import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2GSLTDerivedTGAD

/-!
# Compiled MM2 typed action decoder

The experiment-facing hard decoder is one product machine.  Every emitted
action advances both the language-independent native preorder construction
state and the MM2 source-derived typed frontier.  Failure of either component
rejects the action; neither component can silently substitute for the other.

The relational transition below is independent of the executable product.
Its adequacy theorem states exactly what the runtime must implement.  Reader
admission remains a terminal witness over the resolved completed program, so
incremental construction, MM2 role refinement, and generated parsing are not
collapsed into one self-validating definition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2CompiledDecoder

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec

namespace Native

abbrev Config := NativePreorderConstruction.Config
abbrev State := NativePreorderConstruction.State
abbrev Steps := NativePreorderConstruction.Steps

end Native


namespace Typed


abbrev State := MM2NativeTypedRefinement.PrefixState

/-- Independent relational account of one typed-frontier transition. -/
def Steps (symbols : List String) (state : State)
    (action : Action) (next : State) : Prop :=
  ∃ (expected : MM2NativeTypedRefinement.Expected)
      (rest children : List MM2NativeTypedRefinement.Expected),
    state = expected :: rest ∧
      MM2NativeTypedRefinement.Classifies symbols action expected children ∧
      next = children ++ rest

/-- The executable typed step agrees exactly with the independent relational
transition. -/
theorem step?_eq_some_iff (symbols : List String) (state next : State)
    (action : Action) :
    MM2NativeTypedRefinement.step? symbols state action = some next ↔
      Steps symbols state action next := by
  constructor
  · intro stepped
    rcases MM2NativeTypedRefinement.step?_some_classified
        symbols state next action stepped with
      ⟨expected, rest, children, stateExact, classified, nextExact⟩
    exact ⟨expected, rest, children, stateExact, classified, nextExact⟩
  · rintro ⟨expected, rest, children, rfl, classified, rfl⟩
    simp [MM2NativeTypedRefinement.step?,
      MM2NativeTypedRefinement.compileChildren?_complete
        symbols expected action children classified]

end Typed


/-- Complete state of the product hard decoder. -/
structure State where
  native : Native.State
  typed : Typed.State
  deriving Repr, DecidableEq

def initial : State :=
  { native := NativePreorderConstruction.initial
    typed := MM2NativeTypedRefinement.initial }

/-- Executable hard transition.  The same action must advance both pure
component machines from the same product state. -/
def step? (config : Native.Config) (symbols : List String)
    (state : State) (action : Action) : Option State := do
  let nextNative ← NativePreorderConstruction.step?
    config symbols.length state.native action
  let nextTyped ← MM2NativeTypedRefinement.step?
    symbols state.typed action
  pure { native := nextNative, typed := nextTyped }

/-- Independent relational specification of the hard product transition. -/
structure Steps (config : Native.Config) (symbols : List String)
    (state : State) (action : Action) (next : State) : Prop where
  native : Native.Steps config symbols.length
    state.native action next.native
  typed : Typed.Steps symbols state.typed action next.typed

/-- Executable product transition is adequate for the conjunction of the
native and MM2-typed transition relations. -/
theorem step?_eq_some_iff (config : Native.Config) (symbols : List String)
    (state next : State) (action : Action) :
    step? config symbols state action = some next ↔
      Steps config symbols state action next := by
  unfold step?
  cases nativeStep : NativePreorderConstruction.step?
      config symbols.length state.native action with
  | none =>
      constructor
      · simp
      · intro steps
        have := (NativePreorderConstruction.step?_eq_some_iff
          config symbols.length state.native next.native action).mpr
            steps.native
        rw [nativeStep] at this
        contradiction
  | some nextNative =>
      cases typedStep : MM2NativeTypedRefinement.step?
          symbols state.typed action with
      | none =>
          constructor
          · simp
          · intro steps
            have := (Typed.step?_eq_some_iff symbols state.typed
              next.typed action).mpr steps.typed
            rw [typedStep] at this
            contradiction
      | some nextTyped =>
          constructor
          · intro productStep
            have nextExact :
                ({ native := nextNative, typed := nextTyped } : State) = next := by
              simpa [nativeStep, typedStep] using Option.some.inj productStep
            subst next
            exact {
              native :=
                (NativePreorderConstruction.step?_eq_some_iff
                  config symbols.length state.native nextNative action).mp
                    nativeStep
              typed :=
                (Typed.step?_eq_some_iff symbols state.typed nextTyped action).mp
                  typedStep }
          · intro steps
            have nativeExact :=
              (NativePreorderConstruction.step?_eq_some_iff
                config symbols.length state.native next.native action).mpr
                  steps.native
            have typedExact :=
              (Typed.step?_eq_some_iff symbols state.typed next.typed action).mpr
                steps.typed
            rw [nativeStep] at nativeExact
            rw [typedStep] at typedExact
            cases Option.some.inj nativeExact
            cases Option.some.inj typedExact
            rfl

def run? (config : Native.Config) (symbols : List String) :
    State → List Action → Option State
  | state, [] => some state
  | state, action :: actions => do
      let next ← step? config symbols state action
      run? config symbols next actions

/-- Running the product is exactly the conjunction of running both component
machines on the same action trace. -/
theorem run?_eq_some_iff (config : Native.Config) (symbols : List String) :
    ∀ (state next : State) (actions : List Action),
      run? config symbols state actions = some next ↔
        NativePreorderConstruction.run? config symbols.length
            state.native actions = some next.native ∧
          MM2NativeTypedRefinement.run? symbols state.typed actions =
            some next.typed := by
  intro state next actions
  induction actions generalizing state next with
  | nil =>
      constructor
      · intro exactState
        cases Option.some.inj exactState
        exact ⟨rfl, rfl⟩
      · rintro ⟨nativeExact, typedExact⟩
        have nativeEq : state.native = next.native := Option.some.inj nativeExact
        have typedEq : state.typed = next.typed := Option.some.inj typedExact
        cases state
        cases next
        simp_all [run?, NativePreorderConstruction.run?,
          MM2NativeTypedRefinement.run?]
  | cons action actions induction =>
      simp only [run?, NativePreorderConstruction.run?,
        MM2NativeTypedRefinement.run?]
      cases nativeStep : NativePreorderConstruction.step?
          config symbols.length state.native action with
      | none => simp [step?, nativeStep]
      | some nextNative =>
          cases typedStep : MM2NativeTypedRefinement.step?
              symbols state.typed action with
          | none => simp [step?, typedStep]
          | some nextTyped =>
              simpa [step?, nativeStep, typedStep] using
                induction
                  ({ native := nextNative, typed := nextTyped } : State) next

theorem run?_append (config : Native.Config) (symbols : List String)
    (state : State) (first second : List Action) :
    run? config symbols state (first ++ second) =
      (run? config symbols state first).bind fun middle =>
        run? config symbols middle second := by
  induction first generalizing state with
  | nil => rfl
  | cons action actions induction =>
      simp only [List.cons_append, run?]
      cases stepped : step? config symbols state action with
      | none => simp
      | some next => simpa [stepped] using induction next

/-- Terminal product admission plus the independent generated-reader
witness. -/
structure Admission (config : Native.Config) (symbols : List String)
    (actions : List Action) where
  finalState : State
  runExact : run? config symbols initial actions = some finalState
  nativeComplete : finalState.native.holes = []
  typedComplete : finalState.typed = []
  reader : MM2NativeActionCodec.GSLTAdmission symbols actions

/-- A terminally admitted action trace is exactly the canonical native
preorder encoding of the program carried by its independent reader witness. -/
theorem Admission.actions_eq_native_encoding
    {config : Native.Config} {symbols : List String} {actions : List Action}
    (admission : Admission config symbols actions) :
    actions = encodeProgram admission.reader.nativeProgram :=
  ParsesProgram.actions_eq_encodeProgram admission.reader.actionDecode

/-- The generated MM2 parser does not merely accept some rendering with the
same input bytes: its CST lowering recovers the exact resolved atom program
constructed by the native action trace. -/
theorem Admission.generated_parser_lowers_exactly
    {config : Native.Config} {symbols : List String} {actions : List Action}
    (admission : Admission config symbols actions) :
    admission.reader.parsed.atoms = admission.reader.atoms :=
  admission.reader.parsedAtomsExact

/-- The earlier declarative three-way admission constructs an executable
terminal witness for the product machine. -/
theorem ofDeclarativeAdmission
    {config : Native.Config} {symbols : List String} {actions : List Action}
    (admission : MM2GSLTDerivedTGAD.Admission config symbols actions) :
    Nonempty (Admission config symbols actions) := by
  let finalState : State :=
    { native := admission.structural.finalState, typed := [] }
  have nativeRun := admission.structural.runExact
  have typedRun :=
    MM2NativeTypedRefinement.derived_program_completes admission.typed
  have productRun : run? config symbols initial actions = some finalState :=
    (run?_eq_some_iff config symbols initial finalState actions).mpr
      ⟨nativeRun, typedRun⟩
  exact ⟨{
    finalState := finalState
    runExact := productRun
    nativeComplete := admission.structural.complete
    typedComplete := rfl
    reader := admission.reader }⟩

/-- Every prefix of a terminally admitted trace reaches an explicit product
state. -/
theorem admitted_prefix_non_stranding
    {config : Native.Config} {symbols : List String}
    {actions leading : List Action}
    (admission : Admission config symbols actions)
    (isPrefix : leading <+: actions) :
    ∃ state, run? config symbols initial leading = some state := by
  rcases isPrefix with ⟨suffix, rfl⟩
  have whole := admission.runExact
  rw [run?_append] at whole
  cases prefixRun : run? config symbols initial leading with
  | none => simp [prefixRun] at whole
  | some state => exact ⟨state, rfl⟩

/-! ## Strictness and positive controls -/

private def fixtureConfig : Native.Config :=
  { maxProgramForms := 2
    maxListArity := 6
    maxSymbols := 4
    maxVariables := 4
    maxActions := 20 }

private def wrongAritySymbols : List String := ["exec", "location"]

private def wrongArityProgram : List NativeAtom :=
  [.expression [.reference 0, .reference 1]]

/-- The native construction component accepts and completes the wrong-arity
tree, isolating the strictness contribution of the MM2 typed component. -/
theorem native_component_accepts_wrong_exec_arity :
    ∃ finalState,
      NativePreorderConstruction.run? fixtureConfig
          wrongAritySymbols.length NativePreorderConstruction.initial
          (encodeProgram wrongArityProgram) = some finalState ∧
        finalState.holes = [] := by
  decide +kernel

/-- The actual product decoder rejects the same native-valid action trace. -/
theorem product_rejects_wrong_exec_arity :
    run? fixtureConfig wrongAritySymbols initial
      (encodeProgram wrongArityProgram) = none := by
  decide +kernel

private def correctSymbols : List String := ["exec", "location", ","]

private def correctProgram : List NativeAtom :=
  [.expression
    [.reference 0, .reference 1,
      .expression [.reference 2], .expression [.reference 2]]]

/-- Positive control: one compatibility-mode MM2 work directive completes
both components of the product decoder. -/
theorem product_accepts_supported_exec :
    ∃ finalState,
      run? fixtureConfig correctSymbols initial
          (encodeProgram correctProgram) = some finalState ∧
        finalState.native.holes = [] ∧ finalState.typed = [] := by
  decide +kernel

#print axioms Typed.step?_eq_some_iff
#print axioms step?_eq_some_iff
#print axioms run?_eq_some_iff
#print axioms run?_append
#print axioms ofDeclarativeAdmission
#print axioms Admission.actions_eq_native_encoding
#print axioms Admission.generated_parser_lowers_exactly
#print axioms admitted_prefix_non_stranding
#print axioms native_component_accepts_wrong_exec_arity
#print axioms product_rejects_wrong_exec_arity
#print axioms product_accepts_supported_exec

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2CompiledDecoder
