import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedRuntimeTyping

/-!
# Qualified local control of the polarized Need machine

Continuations consume independently typed runtime answers; captured bodies
retain source derivations and lexical environments. Proof-side native input
conversion preserves source conversion tails without adding an operational
conversion instruction. Demand and allocation resumptions remain distinct.

Only native primitive faults and protocol-shaped retry reasons are admitted
outcomes. This classifies reasons, not the event or receipt that produced
them. Administrative polarity mismatches and a missed local transition are
excluded. Local interception and the unintercepted reference
action are qualified separately against their actual executable definitions.
These local laws are inputs to whole-stack and heap preservation, not a
normalization or arbitrary-effect adequacy claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace PolarizedNeedMachine

open PrimeNeedReference PolarizedNeed
open ScopedComputation (OperationSignature OperationFormation)

variable {Head Operation Effect StableFault NativeFault : Type} {m n v k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- Permitted primitive-domain faults and protocol-shaped reasons, without
an event-origin claim. No administrative source-polarity fault has a constructor. -/
inductive RetryTyping : RetryReason (Fault NativeFault) → Prop where
  | native (fault : NativeFault) : RetryTyping (.domain (.native fault))
  | blackhole (cell : CellId) : RetryTyping (.blackhole cell)
  | outOfScope (cell : CellId) : RetryTyping (.outOfScope cell)
  | noRule (cell : CellId) : RetryTyping (.noRule cell)
  | ownershipLost (cell : CellId) (expected actual : EvaluatorId) :
      RetryTyping (.ownershipLost cell expected actual)
  | allocationCollision (cell : CellId) : RetryTyping (.allocationCollision cell)

theorem liftRetry_typed (reason : RetryReason NativeFault) : RetryTyping (liftRetry reason) := by
  cases reason <;> constructor

theorem RetryTyping.domain_iff_native (fault : Fault NativeFault) :
    RetryTyping (.domain fault) ↔ ∃ native, fault = .native native := by
  constructor
  · intro typed
    cases typed with
    | native fault => exact ⟨fault, rfl⟩
  · rintro ⟨native, rfl⟩
    exact .native native

theorem administrative_retry_not_typed (fault : Fault NativeFault)
    (administrative : ∀ native, fault ≠ .native native) : ¬ RetryTyping (.domain fault) := by
  intro typed
  obtain ⟨native, equal⟩ := (RetryTyping.domain_iff_native fault).mp typed
  exact administrative native equal

inductive OutcomeTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    CTy Head m → Outcome Head Operation Effect StableFault NativeFault m → Prop where
  | value {A : CTy Head m} {answer : Answer Head Operation Effect m} :
      AnswerTyping R signature Δ types answer A → OutcomeTyping R signature Δ types A (.value answer)
  | stableFault {A : CTy Head m} (fault : StableFault) :
      OutcomeTyping R signature Δ types A (.stableFault fault)
  | retryableFault {A : CTy Head m} (reason : RetryReason (Fault NativeFault)) :
      RetryTyping reason → OutcomeTyping R signature Δ types A (.retryableFault reason)

theorem OutcomeTyping.extend {before after : CellTypes Head m} {A : CTy Head m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (typed : OutcomeTyping R signature Δ before A outcome) (extension : StoreExtends before after) :
    OutcomeTyping R signature Δ after A outcome := by
  cases typed with
  | value admitted => exact .value (admitted.extend extension)
  | stableFault fault => exact .stableFault fault
  | retryableFault reason allowed => exact .retryableFault reason allowed

theorem OutcomeTyping.convert {types : CellTypes Head m} {A B : Tm Head m}
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (typed : OutcomeTyping R signature Δ types (.returns (.native A)) outcome)
    (formed : NativeFormation R Δ B) (conversion : Conv R.headEq A B R.computation) :
    OutcomeTyping R signature Δ types (.returns (.native B)) outcome := by
  cases typed with
  | value admitted =>
      cases admitted with
      | returned value => exact .value (.returned (.nativeConv value formed conversion))
  | stableFault fault => exact .stableFault fault
  | retryableFault reason allowed => exact .retryableFault reason allowed

inductive KontTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Kont Head Operation Effect m → CTy Head m → CTy Head m → Prop where
  | done (A : CTy Head m) : KontTyping R signature Δ types .done A A
  | pair {A : Tm Head m} {B : Tm Head (m + 1)} {first : Tm Head m}
      {kont : Kont Head Operation Effect m} {result : CTy Head m} :
      NativeFormation R Δ (.sigma A B) → FormationSensitive.Typing R Δ first A →
      KontTyping R signature Δ types kont (.returns (.native (.sigma A B))) result →
      KontTyping R signature Δ types (.pair first kont) (.returns (.native (inst0 first B))) result
  | nativeApply {A : Tm Head m} {B : CTy Head (m + 1)} {argument : Tm Head m}
      {kont : Kont Head Operation Effect m} {result : CTy Head m} :
      FormationSensitive.Typing R Δ argument A →
      KontTyping R signature Δ types kont (B.instantiate argument) result →
      KontTyping R signature Δ types (.nativeApply argument kont) (.nativePi A B) result
  | valueApply {A : VTy Head m} {B : CTy Head m} {argument : RuntimeValue Head Operation Effect m}
      {kont : Kont Head Operation Effect m} {result : CTy Head m} :
      RuntimeValueTyping R signature Δ types argument A →
      KontTyping R signature Δ types kont B result →
      KontTyping R signature Δ types (.valueApply argument kont) (.arrow A B) result
  | inputConversion {A B : Tm Head m} {result : CTy Head m} {kont : Kont Head Operation Effect m} :
      NativeFormation R Δ B → Conv R.headEq A B R.computation →
      KontTyping R signature Δ types kont (.returns (.native B)) result →
      KontTyping R signature Δ types kont (.returns (.native A)) result

theorem KontTyping.extend {before after : CellTypes Head m}
    {kont : Kont Head Operation Effect m} {A B : CTy Head m}
    (typed : KontTyping R signature Δ before kont A B) (extension : StoreExtends before after) :
    KontTyping R signature Δ after kont A B := by
  induction typed with
  | done A => exact .done A
  | pair formed admitted _ ih => exact .pair formed admitted ih
  | nativeApply admitted _ ih => exact .nativeApply admitted ih
  | valueApply admitted _ ih => exact .valueApply (admitted.extend extension) ih
  | inputConversion formed conversion _ ih => exact .inputConversion formed conversion ih

/-- A demand continuation has no allocation-only Need binder. -/
inductive DemandTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Resume Head Operation Effect m → CTy Head m → CTy Head m → Prop where
  | finish {kont : Kont Head Operation Effect m} {A B : CTy Head m} :
      KontTyping R signature Δ types kont A B → DemandTyping R signature Δ types (.finish kont) A B
  | bindNative {body : NativeBody Head Operation Effect m} {kont : Kont Head Operation Effect m}
      {A : Tm Head m} {B result : CTy Head m} :
      NativeBodyTyping R signature Δ types body A (B.rename wk) →
      KontTyping R signature Δ types kont B result →
      DemandTyping R signature Δ types (.bindNative body kont) (.returns (.native A)) result
  | bindValue {body : ValueBody Head Operation Effect m} {kont : Kont Head Operation Effect m}
      {A : VTy Head m} {B result : CTy Head m} :
      ValueBodyTyping R signature Δ types body A B →
      KontTyping R signature Δ types kont B result →
      DemandTyping R signature Δ types (.bindValue body kont) (.returns A) result
  | bindSigma {body : NativeBody Head Operation Effect m} {kont : Kont Head Operation Effect m}
      {A : Tm Head m} {B : Tm Head (m + 1)} {result : CTy Head m} :
      NativeFormation R Δ (.sigma A B) →
      NativeBodyTyping R signature Δ types body A (.returns (.native B)) →
      KontTyping R signature Δ types kont (.returns (.native (.sigma A B))) result →
      DemandTyping R signature Δ types (.bindSigma body kont) (.returns (.native A)) result

inductive AllocationTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Resume Head Operation Effect m → CTy Head m → CTy Head m → Prop where
  | demand {resume : Resume Head Operation Effect m} {A B : CTy Head m} :
      DemandTyping R signature Δ types resume A B → AllocationTyping R signature Δ types resume A B
  | bindNeed {body : NeedBody Head Operation Effect m} {kont : Kont Head Operation Effect m}
      {A B result : CTy Head m} :
      NeedBodyTyping R signature Δ types body A B →
      KontTyping R signature Δ types kont B result →
      AllocationTyping R signature Δ types (.bindNeed body kont) A result

inductive LocalTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Local Head Operation Effect StableFault NativeFault m → CTy Head m → Prop where
  | evaluate {closure : Closure Head Operation Effect m} {kont : Kont Head Operation Effect m}
      {A B : CTy Head m} :
      ClosureTyping R signature Δ types closure A → KontTyping R signature Δ types kont A B →
      LocalTyping R signature Δ types (.evaluate closure kont) B
  | demand {cell : CellId} {resume : Resume Head Operation Effect m} {A B : CTy Head m} :
      types cell = some A → DemandTyping R signature Δ types resume A B →
      LocalTyping R signature Δ types (.demand cell resume) B
  | complete {outcome : Outcome Head Operation Effect StableFault NativeFault m} {A : CTy Head m} :
      OutcomeTyping R signature Δ types A outcome → LocalTyping R signature Δ types (.complete outcome) A

inductive ActionTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Action (Closure Head Operation Effect m) (Local Head Operation Effect StableFault NativeFault m)
      (Resume Head Operation Effect m) (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect →
        CTy Head m → Prop where
  | done {outcome : Outcome Head Operation Effect StableFault NativeFault m} {A : CTy Head m} :
      OutcomeTyping R signature Δ types A outcome → ActionTyping R signature Δ types (.done outcome) A
  | demand {cell : CellId} {resume : Resume Head Operation Effect m} {A B : CTy Head m} :
      types cell = some A → DemandTyping R signature Δ types resume A B →
      ActionTyping R signature Δ types (.demand cell resume) B
  | allocate {origin : Closure Head Operation Effect m}
      {resume : Resume Head Operation Effect m} {A B : CTy Head m} :
      ClosureTyping R signature Δ types origin A → AllocationTyping R signature Δ types resume A B →
      ActionTyping R signature Δ types (.allocate origin resume) B
  | perform {effect : Effect} {next : Local Head Operation Effect StableFault NativeFault m}
      {A : CTy Head m} :
      LocalTyping R signature Δ types next A → ActionTyping R signature Δ types (.perform effect next) A

theorem DemandTyping.extend {before after : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : CTy Head m}
    (typed : DemandTyping R signature Δ before resume A B) (extension : StoreExtends before after) :
    DemandTyping R signature Δ after resume A B := by
  cases typed with
  | finish kont => exact .finish (kont.extend extension)
  | bindNative body kont => exact .bindNative (body.extend extension) (kont.extend extension)
  | bindValue body kont => exact .bindValue (body.extend extension) (kont.extend extension)
  | bindSigma formed body kont => exact .bindSigma formed (body.extend extension) (kont.extend extension)

theorem AllocationTyping.extend {before after : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : CTy Head m}
    (typed : AllocationTyping R signature Δ before resume A B) (extension : StoreExtends before after) :
    AllocationTyping R signature Δ after resume A B := by
  cases typed with
  | demand demand => exact .demand (demand.extend extension)
  | bindNeed body kont => exact .bindNeed (body.extend extension) (kont.extend extension)

theorem LocalTyping.extend {before after : CellTypes Head m}
    {state : Local Head Operation Effect StableFault NativeFault m} {A : CTy Head m}
    (typed : LocalTyping R signature Δ before state A) (extension : StoreExtends before after) :
    LocalTyping R signature Δ after state A := by
  cases typed with
  | evaluate source kont => exact .evaluate (source.extend extension) (kont.extend extension)
  | demand declared resume => exact .demand (extension _ _ declared) (resume.extend extension)
  | complete outcome => exact .complete (outcome.extend extension)

theorem ActionTyping.extend {before after : CellTypes Head m}
    {current : Action (Closure Head Operation Effect m)
      (Local Head Operation Effect StableFault NativeFault m) (Resume Head Operation Effect m)
      (Answer Head Operation Effect m) StableFault (Fault NativeFault) Effect} {A : CTy Head m}
    (typed : ActionTyping R signature Δ before current A) (extension : StoreExtends before after) :
    ActionTyping R signature Δ after current A := by
  cases typed with
  | done outcome => exact .done (outcome.extend extension)
  | demand declared resume => exact .demand (extension _ _ declared) (resume.extend extension)
  | allocate source resume => exact .allocate (source.extend extension) (resume.extend extension)
  | perform next => exact .perform (next.extend extension)

@[simp] theorem finish_stableFault (fault : StableFault) (kont : Kont Head Operation Effect m) :
    finish (NativeFault := NativeFault) (.stableFault fault) kont = .stableFault fault := by
  cases kont <;> rfl

@[simp] theorem finish_retryableFault (reason : RetryReason (Fault NativeFault))
    (kont : Kont Head Operation Effect m) :
    finish (StableFault := StableFault) (.retryableFault reason) kont = .retryableFault reason := by
  cases kont <;> rfl

@[simp] theorem deliver_stableFault (fault : StableFault) (kont : Kont Head Operation Effect m) :
    deliver (NativeFault := NativeFault) (.stableFault fault) kont = .complete (.stableFault fault) := by
  cases kont <;> rfl

@[simp] theorem deliver_retryableFault (reason : RetryReason (Fault NativeFault))
    (kont : Kont Head Operation Effect m) :
    deliver (StableFault := StableFault) (.retryableFault reason) kont = .complete (.retryableFault reason) := by
  cases kont <;> rfl

private theorem finish_returned_of_equal {types : CellTypes Head m}
    {kont : Kont Head Operation Effect m} {A B : CTy Head m}
    (typed : KontTyping R signature Δ types kont A B) :
    ∀ {V : VTy Head m} {value : RuntimeValue Head Operation Effect m}, A = .returns V →
      RuntimeValueTyping R signature Δ types value V →
      OutcomeTyping (StableFault := StableFault) (NativeFault := NativeFault) R signature Δ types B
        (finish (.value (.returned value)) kont) := by
  match typed with
  | .done _ =>
      intro V value shaped admitted
      cases shaped
      exact .value (.returned admitted)
  | .pair formed firstTyped rest =>
      intro V value shaped admitted
      cases shaped
      obtain ⟨second, rfl, secondTyped⟩ := admitted.native_payload
      obtain ⟨u, universeWitness, formed⟩ := formed
      exact finish_returned_of_equal rest rfl
        (.native (.pairIntro formed universeWitness firstTyped secondTyped))
  | .nativeApply _ _ => intro V value shaped; cases shaped
  | .valueApply _ _ => intro V value shaped; cases shaped
  | .inputConversion formed conversion rest =>
      intro V value shaped admitted
      cases shaped
      exact finish_returned_of_equal rest rfl (.nativeConv admitted formed conversion)
termination_by structural typed

theorem KontTyping.finish_returned {types : CellTypes Head m}
    {kont : Kont Head Operation Effect m} {A : VTy Head m} {B : CTy Head m}
    {value : RuntimeValue Head Operation Effect m}
    (typed : KontTyping R signature Δ types kont (.returns A) B)
    (admitted : RuntimeValueTyping R signature Δ types value A) :
    OutcomeTyping (StableFault := StableFault) (NativeFault := NativeFault) R signature Δ types B
      (finish (.value (.returned value)) kont) :=
  finish_returned_of_equal typed rfl admitted

theorem KontTyping.finish_returner {types : CellTypes Head m}
    {kont : Kont Head Operation Effect m} {A : VTy Head m} {B : CTy Head m}
    (typed : KontTyping R signature Δ types kont (.returns A) B)
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (admitted : OutcomeTyping R signature Δ types (.returns A) outcome) :
    OutcomeTyping R signature Δ types B (finish outcome kont) := by
  cases admitted with
  | value answer =>
      obtain ⟨value, rfl, valueTyped⟩ := answer.returned_payload
      exact typed.finish_returned valueTyped
  | stableFault fault => simpa only [finish_stableFault] using OutcomeTyping.stableFault fault
  | retryableFault reason allowed =>
      simpa only [finish_retryableFault] using OutcomeTyping.retryableFault reason allowed

/-- Delivery can enter a captured computation function. Return-only `finish`
is intentionally not asserted to support every computation-function answer. -/
theorem KontTyping.deliver {types : CellTypes Head m}
    {kont : Kont Head Operation Effect m} {A B : CTy Head m}
    (typed : KontTyping R signature Δ types kont A B)
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (admitted : OutcomeTyping R signature Δ types A outcome) :
    LocalTyping R signature Δ types (deliver outcome kont) B := by
  induction typed generalizing outcome with
  | done _ => exact .complete admitted
  | pair formed firstTyped _ ih =>
      cases admitted with
      | value answer =>
          obtain ⟨value, rfl, valueTyped⟩ := answer.returned_payload
          obtain ⟨second, rfl, secondTyped⟩ := valueTyped.native_payload
          obtain ⟨u, universeWitness, formed⟩ := formed
          exact ih (.value (.returned (.native (.pairIntro formed universeWitness firstTyped secondTyped))))
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason allowed => exact .complete (.retryableFault reason allowed)
  | nativeApply argumentTyped continuation _ =>
      cases admitted with
      | value answer =>
          obtain ⟨body, rfl, bodyTyped⟩ := answer.nativeFunction_payload
          exact .evaluate (bodyTyped.open argumentTyped) continuation
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason allowed => exact .complete (.retryableFault reason allowed)
  | valueApply argumentTyped continuation _ =>
      cases admitted with
      | value answer =>
          obtain ⟨body, rfl, bodyTyped⟩ := answer.valueFunction_payload
          exact .evaluate (bodyTyped.open argumentTyped) continuation
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason allowed => exact .complete (.retryableFault reason allowed)
  | inputConversion formed conversion _ ih => exact ih (admitted.convert formed conversion)

theorem DemandTyping.afterDemand {types : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : CTy Head m}
    (typed : DemandTyping R signature Δ types resume A B)
    {outcome : Outcome Head Operation Effect StableFault NativeFault m}
    (admitted : OutcomeTyping R signature Δ types A outcome) :
    LocalTyping R signature Δ types (afterDemand resume outcome) B := by
  cases typed with
  | finish kont => exact kont.deliver admitted
  | bindNative body kont =>
      cases admitted with
      | value answer =>
          obtain ⟨value, rfl, valueTyped⟩ := answer.returned_payload
          obtain ⟨term, rfl, termTyped⟩ := valueTyped.native_payload
          exact .evaluate (by simpa only [CTy.instantiate_weaken] using body.open termTyped) kont
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason allowed => exact .complete (.retryableFault reason allowed)
  | bindValue body kont =>
      cases admitted with
      | value answer =>
          obtain ⟨value, rfl, valueTyped⟩ := answer.returned_payload
          exact .evaluate (body.open valueTyped) kont
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason allowed => exact .complete (.retryableFault reason allowed)
  | bindSigma formed body kont =>
      cases admitted with
      | value answer =>
          obtain ⟨value, rfl, valueTyped⟩ := answer.returned_payload
          obtain ⟨term, rfl, termTyped⟩ := valueTyped.native_payload
          exact .evaluate (body.open termTyped) (.pair formed termTyped kont)
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason allowed => exact .complete (.retryableFault reason allowed)

theorem AllocationTyping.afterAllocation {types : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : CTy Head m} {cell : CellId}
    (typed : AllocationTyping R signature Δ types resume A B) (declared : types cell = some A) :
    LocalTyping (StableFault := StableFault) (NativeFault := NativeFault)
      R signature Δ types (afterAllocation resume cell) B := by
  cases typed with
  | demand demand => cases demand <;> exact .demand declared (by constructor <;> assumption)
  | bindNeed body kont => exact .evaluate (body.open declared) kont

/-- Native primitive results are checked independently of their signature's
syntax and of the source typing derivation. -/
def PrimitiveSoundness (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m)
    (primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault) : Prop :=
  ∀ operation argument value, OperationFormation R signature operation →
    FormationSensitive.Typing R Δ argument (liftClosed (signature.input operation)) →
    primitive operation argument = .value value →
    FormationSensitive.Typing R Δ value (signature.result operation argument)

theorem PrimitiveSoundness.outcome
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) (operation : Operation)
    {types : CellTypes Head m} {argument : Tm Head m} (formed : OperationFormation R signature operation)
    (admitted : FormationSensitive.Typing R Δ argument (liftClosed (signature.input operation))) :
    OutcomeTyping (Effect := Effect) R signature Δ types
      (.returns (.native (signature.result operation argument))) (liftOutcome (primitive operation argument)) := by
  cases result : primitive operation argument with
  | value value => exact .value (.returned (.native (sound operation argument value formed admitted result)))
  | stableFault fault => exact .stableFault fault
  | retryableFault reason => exact .retryableFault (liftRetry reason) (liftRetry_typed reason)

private theorem source_dispatch {n v k : Nat} {Γ : Ctx Head n}
    {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {code : Computation Head Operation Effect n v k} {A : CTy Head n}
    (source : ComputationTyping R signature Γ sv sn code A)
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) :
    ∀ {types : CellTypes Head m} {native : Sub Head n m}
      {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
      {kont : Kont Head Operation Effect m} {result : CTy Head m},
      EnvironmentTyping R signature Γ sv sn Δ types native values needs →
      KontTyping R signature Δ types kont (A.substitute native) result →
      (∀ next : Local Head Operation Effect StableFault NativeFault m,
        localStep (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont) = some next →
        LocalTyping R signature Δ types next result) ∧
      (localStep (StableFault := StableFault) (NativeFault := NativeFault)
          (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont) = none →
        ActionTyping R signature Δ types
          (action primitive (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont)) result) := by
  match source with
  | .returnValue admitted =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .done (continuation.finish_returned (captureValue_typed admitted environment))
  | .bindNative _ _ first body =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .allocate (.captured first environment)
          (.demand (.bindNative
            (by simpa only [CTy.substitute_weaken] using NativeBodyTyping.captured body environment)
            continuation))
  | .bindValue _ _ first body =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .allocate (.captured first environment)
          (.demand (.bindValue (.captured body environment) continuation))
  | .sequenceSigma formed first body =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .allocate (.captured first environment)
          (.demand (.bindSigma (formed.substitute environment.native)
            (.captured body environment) continuation))
  | .nativeLambda formedA formedB body =>
      intro types native values needs kont result environment continuation
      cases continuation with
      | done _ =>
          refine ⟨?_, ?_⟩
          · intro next selected
            cases selected
          · intro _
            exact .done (.value (.nativeFunction (formedA.substitute environment.native)
              (formedB.substitute (environment.native.lift _)) (.captured body environment)))
      | nativeApply argumentTyped continuation =>
          refine ⟨?_, ?_⟩
          · intro next selected
            cases selected
            exact .evaluate ((NativeBodyTyping.captured body environment).open argumentTyped) continuation
          · intro selected
            cases selected
  | .nativeApply function argument =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
        exact .evaluate (.captured function environment)
          (.nativeApply (argument.substitute environment.native)
            (by simpa only [CTy.substitute_instantiate] using continuation))
      · intro selected
        cases selected
  | .valueLambda formedA formedB body =>
      intro types native values needs kont result environment continuation
      cases continuation with
      | done _ =>
          refine ⟨?_, ?_⟩
          · intro next selected
            cases selected
          · intro _
            exact .done (.value (.valueFunction (formedA.substitute environment.native)
              (formedB.substitute environment.native) (.captured body environment)))
      | valueApply argumentTyped continuation =>
          refine ⟨?_, ?_⟩
          · intro next selected
            cases selected
            exact .evaluate ((ValueBodyTyping.captured body environment).open argumentTyped) continuation
          · intro selected
            cases selected
  | .valueApply function argument =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
        exact .evaluate (.captured function environment)
          (.valueApply (captureValue_typed argument environment) continuation)
      · intro selected
        cases selected
  | .forceThunk value =>
      intro types native values needs kont result environment continuation
      obtain ⟨cn, cv, ck, capturedCode, capturedNative, capturedValues, capturedNeeds,
        shaped, capturedTyped⟩ := (captureValue_typed value environment).thunk_payload
      refine ⟨?_, ?_⟩
      · intro next selected
        simp only [localStep, shaped] at selected
        cases selected
        exact .evaluate capturedTyped continuation
      · intro selected
        simp only [localStep, shaped, reduceCtorEq] at selected
  | .unpackNative _ _ _ value body =>
      intro types native values needs kont result environment continuation
      obtain ⟨index, payload, shaped, indexTyped, payloadTyped⟩ :=
        (captureValue_typed value environment).pair_payload
      refine ⟨?_, ?_⟩
      · intro next selected
        simp only [localStep, shaped] at selected
        cases selected
        exact .evaluate ((PairBodyTyping.captured body environment).open indexTyped payloadTyped) continuation
      · intro selected
        simp only [localStep, shaped, reduceCtorEq] at selected
  | .choose left right =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .allocate (.captured (.choose left right) environment) (.demand (.finish continuation))
  | .call declared admitted =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        have argument := admitted.substitute environment.native
        rw [subst_liftClosed] at argument
        have outcome := sound.outcome _ (Effect := Effect) (types := types) declared argument
        rw [← OperationSignature.substitute_result] at outcome
        exact .done (continuation.finish_returner outcome)
  | .emit next =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .perform (.evaluate (.captured next environment) continuation)
  | .letNeed _ _ suspended body =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .allocate (.captured suspended environment) (.bindNeed (.captured body environment) continuation)
  | .forceNeed index =>
      intro types native values needs kont result environment continuation
      refine ⟨?_, ?_⟩
      · intro next selected
        cases selected
      · intro _
        exact .demand (environment.needs index) (.finish continuation)
  | .nativeConv prior formed conversion =>
      intro types native values needs kont result environment continuation
      exact source_dispatch prior sound environment
        (.inputConversion (formed.substitute environment.native) (conversion.substitute native) continuation)
termination_by structural source

private theorem closure_dispatch {types : CellTypes Head m}
    {closure : Closure Head Operation Effect m} {A : CTy Head m}
    (source : ClosureTyping R signature Δ types closure A)
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) :
    ∀ {kont : Kont Head Operation Effect m} {result : CTy Head m},
      KontTyping R signature Δ types kont A result →
      (∀ next : Local Head Operation Effect StableFault NativeFault m,
        localStep (.evaluate closure kont) = some next → LocalTyping R signature Δ types next result) ∧
      (localStep (StableFault := StableFault) (NativeFault := NativeFault) (.evaluate closure kont) = none →
        ActionTyping R signature Δ types (action primitive (.evaluate closure kont)) result) := by
  match source with
  | .captured source environment =>
      intro kont result continuation
      exact source_dispatch source sound environment continuation
  | .nativeConv prior formed conversion =>
      intro kont result continuation
      exact closure_dispatch prior sound (.inputConversion formed conversion continuation)
termination_by structural source

/-- Qualification of the reference action is used only when local interception
does not apply; the raw fallback's administrative fault is not licensed. -/
theorem LocalTyping.action {types : CellTypes Head m}
    {state : Local Head Operation Effect StableFault NativeFault m} {A : CTy Head m}
    (typed : LocalTyping R signature Δ types state A)
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) (fallback : localStep state = none) :
    ActionTyping R signature Δ types (action primitive state) A := by
  cases typed with
  | evaluate source continuation => exact ((closure_dispatch source sound) continuation).2 fallback
  | demand declared resume => exact .demand declared resume
  | complete outcome => exact .done outcome

theorem LocalTyping.localStep {types : CellTypes Head m}
    {state next : Local Head Operation Effect StableFault NativeFault m} {A : CTy Head m}
    (typed : LocalTyping R signature Δ types state A)
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) (selected : localStep state = some next) :
    LocalTyping R signature Δ types next A := by
  cases typed with
  | evaluate source continuation => exact ((closure_dispatch source sound) continuation).1 next selected
  | demand _ _ => cases selected
  | complete _ => cases selected

private theorem source_choice {n v k : Nat} {Γ : Ctx Head n}
    {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {code : Computation Head Operation Effect n v k} {A : CTy Head n}
    (source : ComputationTyping R signature Γ sv sn code A) :
    ∀ {left right}, code = .choose left right →
      ComputationTyping R signature Γ sv sn left A ∧ ComputationTyping R signature Γ sv sn right A := by
  match source with
  | .choose left right => intro l r equal; cases equal; exact ⟨left, right⟩
  | .nativeConv prior formed conversion =>
      intro left right equal
      obtain ⟨leftTyped, rightTyped⟩ := source_choice prior equal
      exact ⟨.nativeConv leftTyped formed conversion, .nativeConv rightTyped formed conversion⟩
  | .returnValue _ => intro left right equal; cases equal
  | .bindNative _ _ _ _ => intro left right equal; cases equal
  | .bindValue _ _ _ _ => intro left right equal; cases equal
  | .sequenceSigma _ _ _ => intro left right equal; cases equal
  | .nativeLambda _ _ _ => intro left right equal; cases equal
  | .nativeApply _ _ => intro left right equal; cases equal
  | .valueLambda _ _ _ => intro left right equal; cases equal
  | .valueApply _ _ => intro left right equal; cases equal
  | .forceThunk _ => intro left right equal; cases equal
  | .unpackNative _ _ _ _ _ => intro left right equal; cases equal
  | .call _ _ => intro left right equal; cases equal
  | .emit _ => intro left right equal; cases equal
  | .letNeed _ _ _ _ => intro left right equal; cases equal
  | .forceNeed _ => intro left right equal; cases equal
termination_by structural source

private theorem alternative_closure {types : CellTypes Head m}
    {origin : Closure Head Operation Effect m} {A : CTy Head m}
    (typed : ClosureTyping R signature Δ types origin A) :
    ∀ {rule : Rule} {state : Local Head Operation Effect StableFault NativeFault m},
      (rule, state) ∈ alternatives origin →
      ∃ closure, state = .evaluate closure .done ∧ ClosureTyping R signature Δ types closure A := by
  match typed with
  | @ClosureTyping.captured _ _ _ _ _ _ _ _ n v k Γ sv sn code B native values needs source environment =>
      intro rule state member
      cases code with
      | choose left right =>
          obtain ⟨leftTyped, rightTyped⟩ := source_choice source rfl
          simp only [alternatives, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with member | member
          · cases member
            exact ⟨_, rfl, .captured leftTyped environment⟩
          · cases member
            exact ⟨_, rfl, .captured rightTyped environment⟩
      | _ =>
          simp only [alternatives, List.mem_singleton] at member
          cases member
          exact ⟨_, rfl, .captured source environment⟩
  | .nativeConv prior formed conversion =>
      intro rule state member
      obtain ⟨closure, equal, admitted⟩ := alternative_closure prior member
      exact ⟨closure, equal, .nativeConv admitted formed conversion⟩
termination_by structural typed

/-- Every actual alternative retains its origin's type, including source and
captured conversion tails. The ordered alternatives are not deduplicated. -/
theorem ClosureTyping.alternatives {types : CellTypes Head m}
    {origin : Closure Head Operation Effect m} {A : CTy Head m}
    (typed : ClosureTyping R signature Δ types origin A)
    {rule : Rule} {state : Local Head Operation Effect StableFault NativeFault m}
    (member : (rule, state) ∈ alternatives origin) : LocalTyping R signature Δ types state A := by
  obtain ⟨closure, rfl, admitted⟩ := alternative_closure typed member
  exact .evaluate admitted (.done A)

theorem not_demand_bindNeed {types : CellTypes Head m}
    (body : NeedBody Head Operation Effect m) (kont : Kont Head Operation Effect m) (A B : CTy Head m) :
    ¬ DemandTyping R signature Δ types (.bindNeed body kont) A B := by
  intro typed
  cases typed

theorem no_administrative_outcome {types : CellTypes Head m} {A : CTy Head m}
    (fault : Fault NativeFault) (administrative : ∀ native, fault ≠ .native native) :
    ¬ OutcomeTyping (StableFault := StableFault) (Effect := Effect) R signature Δ types A
      (.retryableFault (.domain fault)) := by
  intro typed
  cases typed with
  | retryableFault _ allowed => exact administrative_retry_not_typed fault administrative allowed

/-- An independently admitted thunk body enters its own captured source;
the control transition is the actual local-step equation. -/
theorem admitted_ordinary_force {Γ : Ctx Head n} {sv : Fin v → VTy Head n} {sn : Fin k → CTy Head n}
    {code : Computation Head Operation Effect n v k} {B : CTy Head n}
    (source : ComputationTyping R signature Γ sv sn code B)
    {types : CellTypes Head m} {native : Sub Head n m}
    {values : Fin v → RuntimeValue Head Operation Effect m} {needs : Fin k → CellId}
    (environment : EnvironmentTyping R signature Γ sv sn Δ types native values needs)
    {kont : Kont Head Operation Effect m} {result : CTy Head m}
    (continuation : KontTyping R signature Δ types kont (B.substitute native) result) :
    LocalTyping (StableFault := StableFault) (NativeFault := NativeFault) R signature Δ types
      (.evaluate ⟨n, v, k, .forceThunk (.thunk code), native, values, needs⟩ kont) result ∧
    localStep (StableFault := StableFault) (NativeFault := NativeFault)
      (.evaluate ⟨n, v, k, .forceThunk (.thunk code), native, values, needs⟩ kont) =
      some (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont) ∧
    LocalTyping (StableFault := StableFault) (NativeFault := NativeFault) R signature Δ types
      (.evaluate ⟨n, v, k, code, native, values, needs⟩ kont) result :=
  ⟨.evaluate (.captured (.forceThunk (.thunk source)) environment) continuation,
    rfl, .evaluate (.captured source environment) continuation⟩

theorem expected_thunk_not_admitted {types : CellTypes Head m} {A : CTy Head m} :
    ¬ OutcomeTyping (StableFault := StableFault) (NativeFault := NativeFault) (Effect := Effect)
      R signature Δ types A (.retryableFault (.domain .expectedThunk)) :=
  no_administrative_outcome .expectedThunk (by intro native equal; cases equal)

theorem missed_local_transition_not_admitted {types : CellTypes Head m} {A : CTy Head m} :
    ¬ OutcomeTyping (StableFault := StableFault) (NativeFault := NativeFault) (Effect := Effect)
      R signature Δ types A (.retryableFault (.domain .localTransitionRequired)) :=
  no_administrative_outcome .localTransitionRequired (by intro native equal; cases equal)

theorem allocation_resume_demand_not_admitted {types : CellTypes Head m} {A : CTy Head m} :
    ¬ OutcomeTyping (StableFault := StableFault) (NativeFault := NativeFault) (Effect := Effect)
      R signature Δ types A (.retryableFault (.domain .allocationResumeDemanded)) :=
  no_administrative_outcome .allocationResumeDemanded (by intro native equal; cases equal)

#print axioms RetryTyping.domain_iff_native
#print axioms OutcomeTyping.extend
#print axioms KontTyping.finish_returned
#print axioms KontTyping.deliver
#print axioms DemandTyping.afterDemand
#print axioms AllocationTyping.afterAllocation
#print axioms PrimitiveSoundness.outcome
#print axioms LocalTyping.action
#print axioms LocalTyping.localStep
#print axioms ClosureTyping.alternatives
#print axioms no_administrative_outcome
#print axioms admitted_ordinary_force
#print axioms expected_thunk_not_admitted
#print axioms missed_local_transition_not_admitted
#print axioms allocation_resume_demand_not_admitted

end PolarizedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
