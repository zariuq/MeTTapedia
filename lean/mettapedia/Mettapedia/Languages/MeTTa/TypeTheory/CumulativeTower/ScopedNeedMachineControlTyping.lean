import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedNeedMachineTyping

/-!
# Independent typing of scoped Need-machine control

Demand resumptions consume native outcomes; allocation resumptions receive a
new cell identity. Their typing relations retain captured source derivations
and native environments. Source conversion tails are preserved by a typed
input conversion on the unchanged native continuation, with independent target
formation. No conversion instruction is added to the evaluator.

Local actions are qualified against the actual machine interpretation.
Primitive values require an independent instantiated-signature soundness
contract; stable and retryable faults remain distinct non-value outcomes.
Store extension transports older references without changing their types.
These language-local results are inputs to whole-control and heap preservation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedNeedMachine

open PrimeNeedReference
open ScopedComputation (OperationSignature OperationFormation)
open ScopedNeedComputation (Code weakenNeedTypes extendNeedTypes)

variable {Head Operation Effect StableFault NativeFault : Type} {m n k : Nat}
  {R : Rules Head} {signature : OperationSignature Head Operation} {Δ : Ctx Head m}

/-- Proof-side input conversion keeps the source's native formation evidence;
the operational continuation remains the existing `done`/`pair` syntax. -/
inductive ConversionKontTyping (R : Rules Head) (Δ : Ctx Head m) :
    Kont Head m → Tm Head m → Tm Head m → Prop where
  | done (A : Tm Head m) : ConversionKontTyping R Δ .done A A
  | pair {A : Tm Head m} {B : Tm Head (m + 1)} {u : Head}
      {first : Tm Head m} {kont : Kont Head m} {result : Tm Head m} :
      FormationSensitive.Typing R Δ (.sigma A B) (.head u) → R.isUniverse u →
      FormationSensitive.Typing R Δ first A →
      ConversionKontTyping R Δ kont (.sigma A B) result →
      ConversionKontTyping R Δ (.pair first kont) (inst0 first B) result
  | inputConversion {A B result : Tm Head m} {u : Head} {kont : Kont Head m} :
      FormationSensitive.Typing R Δ B (.head u) → R.isUniverse u →
      Conv R.headEq A B R.computation → ConversionKontTyping R Δ kont B result →
      ConversionKontTyping R Δ kont A result

theorem OutcomeTyping.convert {A B : Tm Head m} {u : Head}
    {outcome : Outcome Head StableFault NativeFault m}
    (typed : OutcomeTyping R Δ A outcome)
    (formed : FormationSensitive.Typing R Δ B (.head u)) (universeWitness : R.isUniverse u)
    (conversion : Conv R.headEq A B R.computation) : OutcomeTyping R Δ B outcome := by
  cases typed with
  | value admitted => exact .value (.conv admitted formed universeWitness conversion)
  | stableFault fault => exact .stableFault fault
  | retryableFault reason => exact .retryableFault reason

theorem ConversionKontTyping.finish_preserves {kont : Kont Head m} {A B : Tm Head m}
    (typed : ConversionKontTyping R Δ kont A B)
    {outcome : Outcome Head StableFault NativeFault m} (admitted : OutcomeTyping R Δ A outcome) :
    OutcomeTyping R Δ B (finish outcome kont) := by
  induction typed generalizing outcome with
  | done _ => exact admitted
  | pair formed universeWitness firstTyped _ ih =>
      cases admitted with
      | value secondTyped =>
          exact ih (.value (.pairIntro formed universeWitness firstTyped secondTyped))
      | stableFault fault => exact .stableFault fault
      | retryableFault reason => exact .retryableFault reason
  | inputConversion formed universeWitness conversion _ ih =>
      exact ih (admitted.convert formed universeWitness conversion)

theorem ConversionKontTyping.convertResult {kont : Kont Head m} {A B C : Tm Head m}
    {u : Head} (typed : ConversionKontTyping R Δ kont A B)
    (formed : FormationSensitive.Typing R Δ C (.head u)) (universeWitness : R.isUniverse u)
    (conversion : Conv R.headEq B C R.computation) : ConversionKontTyping R Δ kont A C := by
  induction typed with
  | done A => exact .inputConversion formed universeWitness conversion (.done C)
  | pair sigmaForm universeSigma firstTyped _ ih =>
      exact .pair sigmaForm universeSigma firstTyped (ih conversion)
  | inputConversion targetForm universeTarget prior _ ih =>
      exact .inputConversion targetForm universeTarget prior (ih conversion)

/-- A demand token contains no allocation-only need binder. Both value-body
constructors retain independently typed source code under the native binder. -/
inductive DemandTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Resume Head Operation Effect m → Tm Head m → Tm Head m → Prop where
  | finish {kont : Kont Head m} {A B : Tm Head m} :
      ConversionKontTyping R Δ kont A B → DemandTyping R signature Δ types (.finish kont) A B
  | bindValue {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {body : Code Head Operation Effect (n + 1) k} {A B : Tm Head n}
      {values : Sub Head n m} {needs : Fin k → CellId} {kont : Kont Head m} {result : Tm Head m} :
      ScopedNeedComputation.Typing R signature (.snoc Γ A)
        (weakenNeedTypes needTypes) body (rename wk B) →
      FormationSensitive.CtxMor R Γ Δ values →
      (∀ index, types (needs index) = some (subst values (needTypes index))) →
      ConversionKontTyping R Δ kont (subst values B) result →
      DemandTyping R signature Δ types (.bindValue ⟨n, k, body, values, needs⟩ kont)
        (subst values A) result
  | bindSigma {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {body : Code Head Operation Effect (n + 1) k} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u : Head} {values : Sub Head n m} {needs : Fin k → CellId}
      {kont : Kont Head m} {result : Tm Head m} :
      FormationSensitive.Typing R Γ (.sigma A B) (.head u) → R.isUniverse u →
      ScopedNeedComputation.Typing R signature (.snoc Γ A) (weakenNeedTypes needTypes) body B →
      FormationSensitive.CtxMor R Γ Δ values →
      (∀ index, types (needs index) = some (subst values (needTypes index))) →
      ConversionKontTyping R Δ kont (subst values (.sigma A B)) result →
      DemandTyping R signature Δ types (.bindSigma ⟨n, k, body, values, needs⟩ kont)
        (subst values A) result

/-- Allocation either continues by demanding the new cell, or opens a source
need binder. The new handle coordinate is separate from native variables. -/
inductive AllocationTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Resume Head Operation Effect m → Tm Head m → Tm Head m → Prop where
  | demand {resume : Resume Head Operation Effect m} {A B : Tm Head m} :
      DemandTyping R signature Δ types resume A B → AllocationTyping R signature Δ types resume A B
  | bindNeed {n k : Nat} {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
      {body : Code Head Operation Effect n (k + 1)} {A B : Tm Head n}
      {values : Sub Head n m} {needs : Fin k → CellId} {kont : Kont Head m} {result : Tm Head m} :
      ScopedNeedComputation.Typing R signature Γ (extendNeedTypes A needTypes) body B →
      FormationSensitive.CtxMor R Γ Δ values →
      (∀ index, types (needs index) = some (subst values (needTypes index))) →
      ConversionKontTyping R Δ kont (subst values B) result →
      AllocationTyping R signature Δ types (.bindNeed ⟨n, k, body, values, needs⟩ kont)
        (subst values A) result

inductive LocalTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Local Head Operation Effect StableFault NativeFault m → Tm Head m → Prop where
  | evaluate {closure : Closure Head Operation Effect m} {kont : Kont Head m} {A B : Tm Head m} :
      ClosureTyping R signature Δ types closure A → ConversionKontTyping R Δ kont A B →
      LocalTyping R signature Δ types (.evaluate closure kont) B
  | demand {cell : CellId} {resume : Resume Head Operation Effect m} {A B : Tm Head m} :
      types cell = some A → DemandTyping R signature Δ types resume A B →
      LocalTyping R signature Δ types (.demand cell resume) B
  | complete {outcome : Outcome Head StableFault NativeFault m} {A : Tm Head m} :
      OutcomeTyping R Δ A outcome → LocalTyping R signature Δ types (.complete outcome) A

inductive ActionTyping (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m) (types : CellTypes Head m) :
    Action (Closure Head Operation Effect m) (Local Head Operation Effect StableFault NativeFault m)
      (Resume Head Operation Effect m) (Tm Head m) StableFault (Fault NativeFault) Effect →
        Tm Head m → Prop where
  | done {outcome : Outcome Head StableFault NativeFault m} {A : Tm Head m} :
      OutcomeTyping R Δ A outcome → ActionTyping R signature Δ types (.done outcome) A
  | demand {cell : CellId} {resume : Resume Head Operation Effect m} {A B : Tm Head m} :
      types cell = some A → DemandTyping R signature Δ types resume A B →
      ActionTyping R signature Δ types (.demand cell resume) B
  | allocate {origin : Closure Head Operation Effect m}
      {resume : Resume Head Operation Effect m} {A B : Tm Head m} :
      ClosureTyping R signature Δ types origin A → AllocationTyping R signature Δ types resume A B →
      ActionTyping R signature Δ types (.allocate origin resume) B
  | perform {effect : Effect} {next : Local Head Operation Effect StableFault NativeFault m}
      {A : Tm Head m} :
      LocalTyping R signature Δ types next A → ActionTyping R signature Δ types (.perform effect next) A

theorem DemandTyping.extend {before after : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : Tm Head m}
    (typed : DemandTyping R signature Δ before resume A B) (extension : StoreExtends before after) :
    DemandTyping R signature Δ after resume A B := by
  cases typed with
  | finish kont => exact .finish kont
  | bindValue body environment references kont =>
      exact .bindValue body environment (fun index => extension _ _ (references index)) kont
  | bindSigma formed universeWitness body environment references kont =>
      exact .bindSigma formed universeWitness body environment
        (fun index => extension _ _ (references index)) kont

theorem AllocationTyping.extend {before after : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : Tm Head m}
    (typed : AllocationTyping R signature Δ before resume A B) (extension : StoreExtends before after) :
    AllocationTyping R signature Δ after resume A B := by
  cases typed with
  | demand demand => exact .demand (demand.extend extension)
  | bindNeed body environment references kont =>
      exact .bindNeed body environment (fun index => extension _ _ (references index)) kont

theorem LocalTyping.extend {before after : CellTypes Head m}
    {state : Local Head Operation Effect StableFault NativeFault m} {A : Tm Head m}
    (typed : LocalTyping R signature Δ before state A) (extension : StoreExtends before after) :
    LocalTyping R signature Δ after state A := by
  cases typed with
  | evaluate source kont => exact .evaluate (source.extend extension) kont
  | demand declared resume => exact .demand (extension _ _ declared) (resume.extend extension)
  | complete outcome => exact .complete outcome

theorem ActionTyping.extend {before after : CellTypes Head m}
    {action : Action (Closure Head Operation Effect m)
      (Local Head Operation Effect StableFault NativeFault m) (Resume Head Operation Effect m)
      (Tm Head m) StableFault (Fault NativeFault) Effect} {A : Tm Head m}
    (typed : ActionTyping R signature Δ before action A) (extension : StoreExtends before after) :
    ActionTyping R signature Δ after action A := by
  cases typed with
  | done outcome => exact .done outcome
  | demand declared resume => exact .demand (extension _ _ declared) (resume.extend extension)
  | allocate source resume => exact .allocate (source.extend extension) (resume.extend extension)
  | perform next => exact .perform (next.extend extension)

theorem DemandTyping.afterDemand {types : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : Tm Head m}
    (typed : DemandTyping R signature Δ types resume A B)
    {outcome : Outcome Head StableFault NativeFault m} (admitted : OutcomeTyping R Δ A outcome) :
    LocalTyping R signature Δ types (afterDemand resume outcome) B := by
  cases typed with
  | finish kont => exact .complete (kont.finish_preserves admitted)
  | bindValue body environment references kont =>
      cases admitted with
      | value valueTyped =>
          apply LocalTyping.evaluate _ kont
          simpa only [subst_liftSub_wk, inst0_rename_wk] using
            value_body_open body environment references valueTyped
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason => exact .complete (.retryableFault reason)
  | bindSigma formed universeWitness body environment references kont =>
      cases admitted with
      | value valueTyped =>
          exact .evaluate (value_body_open body environment references valueTyped)
            (.pair (formed.substitute environment) universeWitness valueTyped kont)
      | stableFault fault => exact .complete (.stableFault fault)
      | retryableFault reason => exact .complete (.retryableFault reason)

theorem AllocationTyping.afterAllocation {types : CellTypes Head m}
    {resume : Resume Head Operation Effect m} {A B : Tm Head m} {cell : CellId}
    (typed : AllocationTyping R signature Δ types resume A B) (declared : types cell = some A) :
    LocalTyping (StableFault := StableFault) (NativeFault := NativeFault)
      R signature Δ types (afterAllocation resume cell) B := by
  cases typed with
  | demand demand => cases demand <;> exact .demand declared (by constructor <;> assumption)
  | bindNeed body environment references kont =>
      exact .evaluate (need_body_open body environment references declared) kont

/-- This is an independent handler obligation on actual primitive value
outputs. It is not supplied by source syntax or by output type metadata. -/
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
    {argument : Tm Head m} (formed : OperationFormation R signature operation)
    (admitted : FormationSensitive.Typing R Δ argument (liftClosed (signature.input operation))) :
    OutcomeTyping R Δ (signature.result operation argument) (liftOutcome (primitive operation argument)) := by
  cases result : primitive operation argument with
  | value value => exact .value (sound operation argument value formed admitted result)
  | stableFault fault => exact .stableFault fault
  | retryableFault reason => exact .retryableFault (liftRetry reason)

private theorem source_action {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
    {code : Code Head Operation Effect n k} {A : Tm Head n}
    (source : ScopedNeedComputation.Typing R signature Γ needTypes code A)
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) :
    ∀ {types : CellTypes Head m} {values : Sub Head n m} {needs : Fin k → CellId}
      {kont : Kont Head m} {result : Tm Head m},
      FormationSensitive.CtxMor R Γ Δ values →
      (∀ index, types (needs index) = some (subst values (needTypes index))) →
      ConversionKontTyping R Δ kont (subst values A) result →
      ActionTyping R signature Δ types
        (action primitive (.evaluate ⟨n, k, code, values, needs⟩ kont)) result := by
  induction source with
  | returnValue admitted =>
      intro types values needs kont result environment references continuation
      exact .done (continuation.finish_preserves (.value (admitted.substitute environment)))
  | sequence formedA universeA formedB universeB first body _ _ =>
      intro types values needs kont result environment references continuation
      exact .allocate (.captured first environment references)
        (.demand (.bindValue body environment references continuation))
  | sequenceSigma formed universeWitness first body _ _ =>
      intro types values needs kont result environment references continuation
      exact .allocate (.captured first environment references)
        (.demand (.bindSigma formed universeWitness body environment references continuation))
  | choose left right _ _ =>
      intro types values needs kont result environment references continuation
      exact .allocate (.captured (.choose left right) environment references) (.demand (.finish continuation))
  | call formed admitted =>
      intro types values needs kont result environment references continuation
      have argument := admitted.substitute environment
      rw [subst_liftClosed] at argument
      have outcome := sound.outcome _ formed argument
      rw [← OperationSignature.substitute_result] at outcome
      exact .done (continuation.finish_preserves outcome)
  | emit next _ =>
      intro types values needs kont result environment references continuation
      exact .perform (.evaluate (.captured next environment references) continuation)
  | letNeed formedA universeA formedB universeB suspended body _ _ =>
      intro types values needs kont result environment references continuation
      exact .allocate (.captured suspended environment references)
        (.bindNeed body environment references continuation)
  | force index =>
      intro types values needs kont result environment references continuation
      exact .demand (references index) (.finish continuation)
  | conv _ formed universeWitness conversion ih =>
      intro types values needs kont result environment references continuation
      exact ih environment references
        (.inputConversion (formed.substitute environment) universeWitness
          (conversion.substitute values) continuation)

theorem LocalTyping.action {types : CellTypes Head m}
    {state : Local Head Operation Effect StableFault NativeFault m} {A : Tm Head m}
    (typed : LocalTyping R signature Δ types state A)
    {primitive : Operation → Tm Head m → Produced (Tm Head m) StableFault NativeFault}
    (sound : PrimitiveSoundness R signature Δ primitive) :
    ActionTyping R signature Δ types (action primitive state) A := by
  cases typed with
  | evaluate source continuation =>
      cases source with
      | captured source environment references =>
          exact source_action source sound environment references continuation
  | demand declared resume => exact .demand declared resume
  | complete outcome => exact .done outcome

private theorem choose_branches {Γ : Ctx Head n} {needTypes : Fin k → Tm Head n}
    {code : Code Head Operation Effect n k} {A : Tm Head n}
    (typed : ScopedNeedComputation.Typing R signature Γ needTypes code A) :
    ∀ {left right}, code = .choose left right →
      ScopedNeedComputation.Typing R signature Γ needTypes left A ∧
        ScopedNeedComputation.Typing R signature Γ needTypes right A := by
  induction typed with
  | choose left right _ _ => intro l r equality; cases equality; exact ⟨left, right⟩
  | conv _ formed universeWitness conversion ih =>
      intro l r equality
      obtain ⟨left, right⟩ := ih equality
      exact ⟨.conv left formed universeWitness conversion, .conv right formed universeWitness conversion⟩
  | _ => intro left right equality; cases equality

/-- Every actual producer alternative retains the origin's displayed type,
including conversion tails on choice. No alternative is selected by typing. -/
theorem ClosureTyping.alternatives {types : CellTypes Head m}
    {origin : Closure Head Operation Effect m} {A : Tm Head m}
    (typed : ClosureTyping R signature Δ types origin A)
    {rule : Rule} {state : Local Head Operation Effect StableFault NativeFault m}
    (member : (rule, state) ∈ alternatives origin) : LocalTyping R signature Δ types state A := by
  cases typed with
  | @captured n k Γ needTypes code B values needs source environment references =>
      cases code with
      | choose left right =>
          obtain ⟨leftTyped, rightTyped⟩ := choose_branches source rfl
          simp only [ScopedNeedMachine.alternatives, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with member | member
          · cases member
            exact .evaluate (.captured leftTyped environment references) (.done _)
          · cases member
            exact .evaluate (.captured rightTyped environment references) (.done _)
      | _ =>
          simp only [ScopedNeedMachine.alternatives, List.mem_singleton] at member
          cases member
          exact .evaluate (.captured source environment references) (.done _)

/-- An allocation-only continuation cannot be licensed for a native demand.
The raw interpreter has a fault for that misuse; typing does not erase it. -/
theorem not_demand_bindNeed {types : CellTypes Head m}
    (body : NeedBody Head Operation Effect m) (kont : Kont Head m) (A B : Tm Head m) :
    ¬ DemandTyping R signature Δ types (.bindNeed body kont) A B := by
  intro typed
  cases typed

namespace ControlExamples

open ScopedNeedComputation.Examples

def primitive : Empty → Tower.Tm 1 → Produced (Tower.Tm 1) Empty Empty :=
  fun operation => nomatch operation

theorem primitive_sound : PrimitiveSoundness Tower.rules operationSignature context primitive := by
  intro operation
  exact nomatch operation

/-- The actual independently typed effectful sharing source starts with a
qualified local allocation action, before any evaluation or heap admission. -/
theorem dependent_source_action :
    ActionTyping Tower.rules operationSignature context (fun _ => none)
      (action primitive (.evaluate ⟨1, 0, source, ids, Fin.elim0⟩ .done))
      (.sigma ground identityFamily) := by
  have captured : ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, source, ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (subst ids (.sigma ground identityFamily)) :=
    .captured source_typing (fun index => by simpa only [subst_ids, ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index))
      (fun index => Fin.elim0 index)
  have typed : LocalTyping (StableFault := Empty) (NativeFault := Empty)
      Tower.rules operationSignature context (fun _ => none)
      (.evaluate ⟨1, 0, source, ids, Fin.elim0⟩ .done)
      (.sigma ground identityFamily) := by
    apply LocalTyping.evaluate _ (.done _)
    simpa only [subst_ids] using captured
  exact typed.action primitive_sound

/-- Treating the source's new-handle body as a value-demand continuation is
rejected independently of what values a primitive or cache might return. -/
theorem need_body_not_demanded (A B : Tower.Tm 1) :
    ¬ DemandTyping Tower.rules operationSignature context (fun _ => none)
      (.bindNeed (⟨1, 0, boundBody, ids, Fin.elim0⟩ : NeedBody Tower.Head Empty Bool 1) .done) A B :=
  not_demand_bindNeed _ _ A B

/-- A type-level beta redex, distinct from its opaque ground normal form. -/
def betaExpanded : Tower.Tm 1 := .app (.lam (ground : Tower.Tm 2)) (.var 0)

theorem betaExpanded_step : Step Tower.HeadEq betaExpanded ground Tower.rules.computation :=
  .betaPi ground (.var 0)

theorem betaExpanded_ne_ground : betaExpanded ≠ (ground : Tower.Tm 1) := by
  intro equal
  cases equal

/-- Formation is derived independently by native Pi formation, lambda
introduction and application, not inferred from the beta conversion. -/
theorem betaExpanded_formed :
    FormationSensitive.Typing Tower.rules context betaExpanded (sortTm Tower.zero) := by
  apply FormationSensitive.Typing.appElim
    (A := ground) (B := sortTm Tower.zero) _ (.var 0)
  apply FormationSensitive.Typing.lamIntro
  · exact .piForm (.headType .legacyGround) (.sort Tower.zero)
      (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
      (.sorts Tower.zero (.succ Tower.zero))
  · exact .sort _
  · exact .headType .legacyGround

theorem ground_converts_betaExpanded :
    Conv Tower.HeadEq (ground : Tower.Tm 1) betaExpanded Tower.rules.computation :=
  .symm _ _ (.rel _ _ betaExpanded_step)

/-- The unchanged `done` continuation changes the displayed result type only
with genuine native beta evidence and the independently formed target. -/
theorem beta_done_conversion :
    ConversionKontTyping Tower.rules context .done ground betaExpanded :=
  .inputConversion betaExpanded_formed (.sort Tower.zero) ground_converts_betaExpanded (.done _)

theorem beta_finish_preserves :
    OutcomeTyping Tower.rules context betaExpanded
      (finish (.value (.var 0) : Outcome Tower.Head Empty Empty 1) .done) :=
  beta_done_conversion.finish_preserves (.value (.var 0))

/-- The actual finished payload keeps full native admission at the beta-
expanded type, although runtime completion has not changed its syntax. -/
theorem beta_finished_judgment :
    FormationSensitive.Judgment Tower.rules context (.var 0) betaExpanded := by
  have admitted := beta_finish_preserves
  cases admitted with
  | value typed => exact ⟨source_judgment.context, typed⟩

/-- A real source conversion tail passes through the generic action theorem;
the machine still returns the original native variable. -/
theorem beta_source_action :
    ActionTyping Tower.rules operationSignature context (fun _ => none)
      (action primitive (.evaluate
        (⟨1, 0, .returnValue (.var 0), ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1) .done))
      betaExpanded := by
  have source : ScopedNeedComputation.Typing Tower.rules operationSignature context noNeeds
      (.returnValue (.var 0) : Code Tower.Head Empty Bool 1 0) betaExpanded :=
    .conv (.returnValue (.var 0)) betaExpanded_formed (.sort Tower.zero) ground_converts_betaExpanded
  have captured : ClosureTyping Tower.rules operationSignature context (fun _ => none)
      (⟨1, 0, .returnValue (.var 0), ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1)
      (subst ids betaExpanded) :=
    .captured source (fun index => by simpa only [subst_ids, ids] using
      (FormationSensitive.Typing.var (R := Tower.rules) (Γ := context) index))
      (fun index => Fin.elim0 index)
  have localTyped : LocalTyping (StableFault := Empty) (NativeFault := Empty)
      Tower.rules operationSignature context (fun _ => none)
      (.evaluate (⟨1, 0, .returnValue (.var 0), ids, Fin.elim0⟩ : Closure Tower.Head Empty Bool 1) .done)
      betaExpanded := by
    apply LocalTyping.evaluate _ (.done _)
    simpa only [subst_ids] using captured
  exact localTyped.action primitive_sound

end ControlExamples

#print axioms ConversionKontTyping.finish_preserves
#print axioms ConversionKontTyping.convertResult
#print axioms DemandTyping.extend
#print axioms AllocationTyping.extend
#print axioms LocalTyping.extend
#print axioms ActionTyping.extend
#print axioms DemandTyping.afterDemand
#print axioms AllocationTyping.afterAllocation
#print axioms PrimitiveSoundness.outcome
#print axioms LocalTyping.action
#print axioms ClosureTyping.alternatives
#print axioms not_demand_bindNeed
#print axioms ControlExamples.dependent_source_action
#print axioms ControlExamples.need_body_not_demanded
#print axioms ControlExamples.betaExpanded_step
#print axioms ControlExamples.betaExpanded_ne_ground
#print axioms ControlExamples.betaExpanded_formed
#print axioms ControlExamples.beta_done_conversion
#print axioms ControlExamples.beta_finish_preserves
#print axioms ControlExamples.beta_finished_judgment
#print axioms ControlExamples.beta_source_action

end ScopedNeedMachine
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
