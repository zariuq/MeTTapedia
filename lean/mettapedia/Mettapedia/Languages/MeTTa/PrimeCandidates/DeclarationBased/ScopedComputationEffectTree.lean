import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternCodec
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.OpaqueRelatorScopedComputation
import Mettapedia.GSLT.LanguageDef.ContextualEffectTreeExactness

/-!
# Scoped native computations at the Bool effect-tree boundary

Native payloads use the existing scope-indexed Pattern codec. Mapping those
payloads through the existing effect program preserves the complete ordered
world list: branch occurrences, states, answers and deferred intent order.
Actual native substitution remains the operation of `Code.interpret`.

The authored effect-tree language executes that mapped program. Qualification
therefore yields exact ordered source worlds and arbitrary-target
no-invention, with native result admission checked separately. The backend
does not normalize native payloads, perform deferred intents, or interpret
the meaning of a represented HOL proposition.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace ScopedComputationEffectTree

open Presentation Presentation.ScopedComputation
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.GSLT.LanguageDef

universe uAnswer uIntent

variable {Answer : Type uAnswer} {Intent : Type uIntent}

/-- Encode only the two payload fields; retain state and occurrence identity. -/
def mapWorld (answerMap : Answer → Pattern) (intentMap : Intent → Pattern)
    (world : WorldResult Bool Answer Intent) : WorldResult Bool Pattern Pattern where
  branch := world.branch
  answer := answerMap world.answer
  state := world.state
  intents := world.intents.map intentMap

/-- Structural payload mapping of the existing effect tree. Both branches of
each Boolean read are retained; this does not run the source program. -/
def mapProgram (answerMap : Answer → Pattern) (intentMap : Intent → Pattern) :
    Program Bool Answer Intent → Program Bool Pattern Pattern
  | .pure answer => .pure (answerMap answer)
  | .choose left right =>
      .choose (mapProgram answerMap intentMap left) (mapProgram answerMap intentMap right)
  | .read next => .read fun state => mapProgram answerMap intentMap (next state)
  | .write state next => .write state (mapProgram answerMap intentMap next)
  | .intent request next => .intent (intentMap request) (mapProgram answerMap intentMap next)

/-- Exact list equality retains multiplicity and authored order, not just
the support of visible answers. -/
theorem mapProgram_worlds (answerMap : Answer → Pattern) (intentMap : Intent → Pattern)
    (program : Program Bool Answer Intent) (state : Bool) (branch : BranchTrace) :
    runWorldsAt (mapProgram answerMap intentMap program) state branch =
      (runWorldsAt program state branch).map (mapWorld answerMap intentMap) := by
  induction program generalizing state branch with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [mapProgram, runWorldsAt, leftIH, rightIH, List.map_append]
  | read next nextIH => exact nextIH state state branch
  | write newState next nextIH => exact nextIH newState branch
  | intent request next nextIH =>
      simp only [mapProgram, runWorldsAt, nextIH, List.map_map]
      rfl

theorem mapWorld_injective (answerMap : Answer → Pattern) (intentMap : Intent → Pattern)
    (answers : Function.Injective answerMap) (intents : Function.Injective intentMap) :
    Function.Injective (mapWorld answerMap intentMap) := by
  intro left right equality
  have branches := congrArg WorldResult.branch equality
  have answer := answers (congrArg WorldResult.answer equality)
  have states := congrArg WorldResult.state equality
  have requests := intents.list_map (congrArg WorldResult.intents equality)
  cases left
  cases right
  cases branches
  cases answer
  cases states
  cases requests
  rfl

variable {Head Operation : Type} {n m k : Nat}

/-- The existing scalar representation supplies the native intent codec. -/
def natCodec : PartialCodec Nat Pattern where
  encode := DeclarationAwarePatternCodec.encodeNat
  decode := DeclarationAwarePatternCodec.decodeNat?
  decode_encode := DeclarationAwarePatternCodec.decodeNat?_encodeNat

/-- A world with scope-checked native answers and separately encoded intents. -/
def payloadWorld (headCodec : PartialCodec Head Pattern) (intentCodec : PartialCodec Intent Pattern) :
    WorldResult Bool (Tm Head m) Intent → WorldResult Bool Pattern Pattern :=
  mapWorld (DeclarationAwarePatternCodec.encodeTm headCodec) intentCodec.encode

theorem payloadWorld_injective (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) :
    Function.Injective (payloadWorld (m := m) headCodec intentCodec) :=
  mapWorld_injective _ _
    (DeclarationAwarePatternCodec.tmCodec headCodec m).encode_injective intentCodec.encode_injective

/-- The backend's existing world-list encoder retains the native payload map. -/
def encodePayloadWorlds (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) (worlds : List (WorldResult Bool (Tm Head m) Intent)) :
    Pattern :=
  ContextualEffectTreeLanguage.encodeWorlds (worlds.map (payloadWorld headCodec intentCodec))

theorem encodePayloadWorlds_injective (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) :
    Function.Injective (encodePayloadWorlds (m := m) headCodec intentCodec) :=
  ContextualEffectTreeLanguage.encodeWorlds_injective.comp
    (payloadWorld_injective headCodec intentCodec).list_map

def payloadCompletion (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) (worlds : List (WorldResult Bool (Tm Head m) Intent)) :
    Pattern :=
  ContextualEffectTreeLanguage.completion (worlds.map (payloadWorld headCodec intentCodec))

theorem payloadCompletion_injective (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) :
    Function.Injective (payloadCompletion (m := m) headCodec intentCodec) :=
  ContextualEffectTreeLanguage.completion_injective.comp
    (payloadWorld_injective headCodec intentCodec).list_map

private theorem decode_intents_encode (intentCodec : PartialCodec Intent Pattern)
    (intents : List Intent) :
    (intents.map intentCodec.encode).mapM intentCodec.decode = some intents := by
  induction intents with
  | nil => rfl
  | cons request requests ih => simp [List.mapM_cons, intentCodec.decode_encode, ih]

/-- Decoding checks the native answer at the advertised target scope. -/
def decodePayloadWorld (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) (scope : Nat)
    (world : WorldResult Bool Pattern Pattern) : Option (WorldResult Bool (Tm Head scope) Intent) :=
  match DeclarationAwarePatternCodec.decodeTm? headCodec scope world.answer with
  | none => none
  | some answer =>
      (world.intents.mapM intentCodec.decode).map fun intents =>
        { branch := world.branch, answer := answer, state := world.state, intents := intents }

@[simp] theorem decodePayloadWorld_payloadWorld (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern) (world : WorldResult Bool (Tm Head m) Intent) :
    decodePayloadWorld headCodec intentCodec m (payloadWorld headCodec intentCodec world) = some world := by
  cases world
  simp only [decodePayloadWorld, payloadWorld, mapWorld,
    DeclarationAwarePatternCodec.decodeTm?_encodeTm, decode_intents_encode, Option.map_some]

/-- Mapping happens after the actual scoped interpreter has instantiated its
native payloads and bound the selected answers in sequence bodies. -/
def payloadProgram (headCodec : PartialCodec Head Pattern) (intentCodec : PartialCodec Intent Pattern)
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (environment : Sub Head n m) (code : Code Head Operation n) : Program Bool Pattern Pattern :=
  mapProgram (DeclarationAwarePatternCodec.encodeTm headCodec) intentCodec.encode
    (Code.interpret implementation.handler environment code)

/-- Qualification connects the mapped handler to independently authored
source world lists for every source code and native environment. -/
theorem payloadProgram_worlds (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : Bool) (branch : BranchTrace) :
    runWorldsAt (payloadProgram headCodec intentCodec implementation environment code) state branch =
      (Code.worlds implementation.primitive environment code state branch).map
        (payloadWorld headCodec intentCodec) := by
  rw [payloadProgram, mapProgram_worlds,
    ImplementationStudy.qualified_worlds implementation qualified]
  rfl

/-- The compilation boundary inherits native lifted-substitution coherence;
it does not implement another binder or a Pattern-level substitution. -/
theorem payloadProgram_substitute (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent k)
    (later : Sub Head m k) (earlier : Sub Head n m) (code : Code Head Operation n) :
    payloadProgram headCodec intentCodec implementation later (code.substitute earlier) =
      payloadProgram headCodec intentCodec implementation (subComp later earlier) code := by
  unfold payloadProgram
  rw [Code.interpret_substitute]

/-- Every mapped result recovers a source world and its full refined native
judgment. The source context, target context and admitted substitution are
independent inputs to the implementation qualification theorem. -/
theorem payloadProgram_results (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    {sourceContext : Ctx Head n} {targetContext : Ctx Head m}
    {code : Code Head Operation n} {resultType : Tm Head n}
    (judgment : Judgment rules signature sourceContext code resultType)
    {environment : Sub Head n m}
    (target : FormationSensitive.ContextFormation rules targetContext)
    (typed : FormationSensitive.CtxMor rules sourceContext targetContext environment)
    {state : Bool} {branch : BranchTrace} {encoded : WorldResult Bool Pattern Pattern}
    (returned : encoded ∈
      runWorldsAt (payloadProgram headCodec intentCodec implementation environment code) state branch) :
    ∃ original ∈ Code.worlds implementation.primitive environment code state branch,
      payloadWorld headCodec intentCodec original = encoded ∧
      decodePayloadWorld headCodec intentCodec m encoded = some original ∧
      FormationSensitive.Judgment rules targetContext original.answer (subst environment resultType) := by
  rw [payloadProgram_worlds headCodec intentCodec implementation qualified] at returned
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp returned
  refine ⟨original, member, rfl, decodePayloadWorld_payloadWorld _ _ _, ?_⟩
  apply ImplementationStudy.qualified_interpretation implementation qualified judgment target typed
  rw [ImplementationStudy.qualified_worlds implementation qualified]
  exact member

/-- Compile the actual scoped interpretation into an initialized authored
effect-tree request. No source worlds are evaluated by this construction. -/
def compile (headCodec : PartialCodec Head Pattern) (intentCodec : PartialCodec Intent Pattern)
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : Bool) (branch : BranchTrace) : Pattern :=
  ContextualEffectTreeLanguage.request
    (payloadProgram headCodec intentCodec implementation environment code) state branch

theorem compile_substitute (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent k)
    (later : Sub Head m k) (earlier : Sub Head n m) (code : Code Head Operation n)
    (state : Bool) (branch : BranchTrace) :
    compile headCodec intentCodec implementation later (code.substitute earlier) state branch =
      compile headCodec intentCodec implementation (subComp later earlier) code state branch := by
  unfold compile
  rw [payloadProgram_substitute]

/-- Sufficient contextual depth gives exactly the independently authored
source worlds. Their order and multiplicity are inside the retained result. -/
theorem qualified_executor_exact (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (fuel : Nat) (state : Bool) (branch : BranchTrace)
    (adequate : ContextualEffectTreeLanguage.depth
      (payloadProgram headCodec intentCodec implementation environment code) ≤ fuel) :
    ContextualEffectTreeLanguage.execute fuel
        (compile headCodec intentCodec implementation environment code state branch) =
      [payloadCompletion headCodec intentCodec
        (Code.worlds implementation.primitive environment code state branch)] := by
  rw [compile, ContextualEffectTreeLanguage.executor_exact fuel _ state branch adequate,
    payloadProgram_worlds headCodec intentCodec implementation qualified]
  rfl

/-- No fuel bound or target-shape premise is needed for no-invention. -/
theorem qualified_executor_no_invention (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (fuel : Nat) (state : Bool) (branch : BranchTrace) (target : Pattern)
    (returned : target ∈ ContextualEffectTreeLanguage.execute fuel
      (compile headCodec intentCodec implementation environment code state branch)) :
    target = payloadCompletion headCodec intentCodec
      (Code.worlds implementation.primitive environment code state branch) := by
  have exactTarget := ContextualEffectTreeLanguage.executor_no_invention fuel
    (payloadProgram headCodec intentCodec implementation environment code) state branch target returned
  rw [payloadProgram_worlds headCodec intentCodec implementation qualified] at exactTarget
  exact exactTarget

/-- The same correspondence holds for the independently authored GSLT
relation, not just for one executable evaluator. -/
theorem qualified_step_iff (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : Bool) (branch : BranchTrace) (target : Pattern) :
    ContextualEffectTreeLanguage.theory.Step
        (compile headCodec intentCodec implementation environment code state branch) target ↔
      target = payloadCompletion headCodec intentCodec
        (Code.worlds implementation.primitive environment code state branch) := by
  rw [compile, ContextualEffectTreeLanguage.theory_step_request_iff,
    payloadProgram_worlds headCodec intentCodec implementation qualified]
  rfl

/-- A backend result has the unique authorized completion and every retained
answer has its actual native dependent type in the admitted target context. -/
theorem qualified_step_results (headCodec : PartialCodec Head Pattern)
    (intentCodec : PartialCodec Intent Pattern)
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : ImplementationStudy.Implementation Head Operation Bool Intent m)
    (qualified : (ImplementationStudy.specification rules signature).Satisfies implementation)
    {sourceContext : Ctx Head n} {targetContext : Ctx Head m}
    {code : Code Head Operation n} {resultType : Tm Head n}
    (judgment : Judgment rules signature sourceContext code resultType)
    {environment : Sub Head n m}
    (formed : FormationSensitive.ContextFormation rules targetContext)
    (typed : FormationSensitive.CtxMor rules sourceContext targetContext environment)
    {state : Bool} {branch : BranchTrace} {target : Pattern}
    (step : ContextualEffectTreeLanguage.theory.Step
      (compile headCodec intentCodec implementation environment code state branch) target) :
    target = payloadCompletion headCodec intentCodec
        (Code.worlds implementation.primitive environment code state branch) ∧
      (∀ world ∈ Code.worlds implementation.primitive environment code state branch,
        FormationSensitive.Judgment rules targetContext world.answer (subst environment resultType)) := by
  refine ⟨(qualified_step_iff headCodec intentCodec implementation qualified environment code
    state branch target).mp step, ?_⟩
  intro world returned
  apply ImplementationStudy.qualified_interpretation implementation qualified judgment formed typed
  rw [ImplementationStudy.qualified_worlds implementation qualified]
  exact returned

/-- The native specialization keeps the full existing term grammar. -/
def nativeProgram {n : Nat} (program : Program Bool (Tower.Tm n) Nat) :
    Program Bool Pattern Pattern :=
  mapProgram (DeclarationAwarePatternCodec.encodeTm DeclarationAwarePatternCodec.towerHeadCodec)
    DeclarationAwarePatternCodec.encodeNat program

def nativeWorld {n : Nat} : WorldResult Bool (Tower.Tm n) Nat → WorldResult Bool Pattern Pattern :=
  payloadWorld DeclarationAwarePatternCodec.towerHeadCodec natCodec

theorem nativeProgram_worlds {n : Nat} (program : Program Bool (Tower.Tm n) Nat)
    (state : Bool) (branch : BranchTrace) :
    runWorldsAt (nativeProgram program) state branch =
      (runWorldsAt program state branch).map nativeWorld :=
  mapProgram_worlds _ _ program state branch

theorem nativeWorld_injective : Function.Injective (nativeWorld (n := n)) :=
  payloadWorld_injective _ _

/-- Complete native world data in the backend's actual fixed alphabet. -/
def encodeWorlds {n : Nat} (worlds : List (WorldResult Bool (Tower.Tm n) Nat)) : Pattern :=
  encodePayloadWorlds DeclarationAwarePatternCodec.towerHeadCodec natCodec worlds

theorem encodeWorlds_injective : Function.Injective (encodeWorlds (n := n)) :=
  encodePayloadWorlds_injective _ _

def completion {n : Nat} (worlds : List (WorldResult Bool (Tower.Tm n) Nat)) : Pattern :=
  payloadCompletion DeclarationAwarePatternCodec.towerHeadCodec natCodec worlds

theorem completion_injective : Function.Injective (completion (n := n)) :=
  payloadCompletion_injective _ _

/-- This request compiles the existing effect tree without running it. -/
def request {n : Nat} (program : Program Bool (Tower.Tm n) Nat)
    (state : Bool) (branch : BranchTrace) : Pattern :=
  ContextualEffectTreeLanguage.request (nativeProgram program) state branch

/-- Arbitrary native effect programs, not only scoped-code images, have the
same exact public completion relation under the authored backend. -/
theorem native_step_iff (program : Program Bool (Tower.Tm n) Nat)
    (state : Bool) (branch : BranchTrace) (target : Pattern) :
    ContextualEffectTreeLanguage.theory.Step (request program state branch) target ↔
      target = completion (runWorldsAt program state branch) := by
  rw [request, ContextualEffectTreeLanguage.theory_step_request_iff, nativeProgram_worlds]
  rfl

theorem native_complete_iff (program : Program Bool (Tower.Tm n) Nat)
    (state : Bool) (branch : BranchTrace) (worlds : List (WorldResult Bool (Tower.Tm n) Nat)) :
    ContextualEffectTreeLanguage.theory.Step (request program state branch) (completion worlds) ↔
      worlds = runWorldsAt program state branch := by
  rw [native_step_iff]
  exact ⟨fun equal => completion_injective equal, congrArg completion⟩

theorem native_executor_exact (program : Program Bool (Tower.Tm n) Nat)
    (fuel : Nat) (state : Bool) (branch : BranchTrace)
    (adequate : ContextualEffectTreeLanguage.depth (nativeProgram program) ≤ fuel) :
    ContextualEffectTreeLanguage.execute fuel (request program state branch) =
      [completion (runWorldsAt program state branch)] := by
  rw [request, ContextualEffectTreeLanguage.executor_exact fuel _ state branch adequate,
    nativeProgram_worlds]
  rfl

theorem native_executor_no_invention (program : Program Bool (Tower.Tm n) Nat)
    (fuel : Nat) (state : Bool) (branch : BranchTrace) (target : Pattern)
    (returned : target ∈ ContextualEffectTreeLanguage.execute fuel (request program state branch)) :
    target = completion (runWorldsAt program state branch) := by
  have exactTarget := ContextualEffectTreeLanguage.executor_no_invention fuel
    (nativeProgram program) state branch target returned
  rw [nativeProgram_worlds] at exactTarget
  exact exactTarget

def decodeWorlds? (scope : Nat) (encoded : Pattern) :
    Option (List (WorldResult Bool (Tower.Tm scope) Nat)) := do
  let worlds ← ContextualEffectTreeLanguage.decodeWorlds? encoded
  worlds.mapM (decodePayloadWorld DeclarationAwarePatternCodec.towerHeadCodec natCodec scope)

@[simp] theorem decodeWorlds?_encodeWorlds (worlds : List (WorldResult Bool (Tower.Tm n) Nat)) :
    decodeWorlds? n (encodeWorlds worlds) = some worlds := by
  simp only [decodeWorlds?, encodeWorlds, encodePayloadWorlds,
    ContextualEffectTreeLanguage.decodeWorlds?_encodeWorlds]
  change (worlds.map nativeWorld).mapM
    (decodePayloadWorld DeclarationAwarePatternCodec.towerHeadCodec natCodec n) = some worlds
  induction worlds with
  | nil => rfl
  | cons world worlds ih =>
      have decoded := decodePayloadWorld_payloadWorld
        DeclarationAwarePatternCodec.towerHeadCodec natCodec world
      change decodePayloadWorld DeclarationAwarePatternCodec.towerHeadCodec natCodec n
        (nativeWorld world) = some world at decoded
      rw [List.map_cons, List.mapM_cons, decoded, ih]
      rfl

namespace Common

open NativeExamples

/-- The actual producer and dependent continuation in the mixed telescope. -/
def program : Program Bool Pattern Pattern :=
  nativeProgram (Code.interpret handler OpaqueRelatorScopedComputation.Common.environment source)

/-- These worlds come from the separately authored primitive lists. -/
def worlds (state : Bool) (branch : BranchTrace) : List (WorldResult Bool (Tower.Tm 3) Nat) :=
  Code.worlds primitiveWorlds OpaqueRelatorScopedComputation.Common.environment source state branch

theorem program_worlds (state : Bool) (branch : BranchTrace) :
    runWorldsAt program state branch = (worlds state branch).map nativeWorld := by
  rw [program, nativeProgram_worlds, Code.interpret_worlds handler primitiveWorlds handler_realizes]
  rfl

theorem worlds_shape (state : Bool) (branch : BranchTrace) :
    worlds state branch =
      [{ branch := false :: branch,
         answer := .pair (OpaqueRelatorScopedComputation.Common.environment 1)
           (.refl (OpaqueRelatorScopedComputation.Common.environment 1)),
         state := true, intents := [10, 30] },
       { branch := true :: branch,
         answer := .pair (OpaqueRelatorScopedComputation.Common.environment 0)
           (.refl (OpaqueRelatorScopedComputation.Common.environment 0)),
         state := false, intents := [20, 40] }] := by
  rw [worlds, ← Code.interpret_worlds handler primitiveWorlds handler_realizes]
  exact OpaqueRelatorScopedComputation.Common.source_worlds state branch

theorem worlds_admitted (state : Bool) (branch : BranchTrace)
    (world : WorldResult Bool (Tower.Tm 3) Nat) (returned : world ∈ worlds state branch) :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules
      OpaqueRelatorScopedComputation.Common.context world.answer
      (subst OpaqueRelatorScopedComputation.Common.environment (.sigma ground identityFamily)) := by
  apply OpaqueRelatorScopedComputation.Common.source_results
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  exact returned

theorem backend_exact (fuel : Nat) (state : Bool) (branch : BranchTrace)
    (adequate : ContextualEffectTreeLanguage.depth program ≤ fuel) :
    ContextualEffectTreeLanguage.execute fuel (ContextualEffectTreeLanguage.request program state branch) =
      [completion (worlds state branch)] := by
  rw [ContextualEffectTreeLanguage.executor_exact fuel program state branch adequate, program_worlds]
  rfl

theorem backend_step_iff (state : Bool) (branch : BranchTrace) (target : Pattern) :
    ContextualEffectTreeLanguage.theory.Step
        (ContextualEffectTreeLanguage.request program state branch) target ↔
      target = completion (worlds state branch) := by
  rw [ContextualEffectTreeLanguage.theory_step_request_iff, program_worlds]
  rfl

/-- Actual mixed source admission, exact backend execution, arbitrary-target
reflection and dependent result admission meet on one native workload. -/
theorem backend_contract (state : Bool) (branch : BranchTrace) :
    Judgment HOLNativeRelatorCompatibility.rules signature OpaqueRelatorScopedComputation.Common.context
        (source.substitute OpaqueRelatorScopedComputation.Common.environment)
        (subst OpaqueRelatorScopedComputation.Common.environment (.sigma ground identityFamily)) ∧
      ContextualEffectTreeLanguage.execute (ContextualEffectTreeLanguage.depth program)
        (ContextualEffectTreeLanguage.request program state branch) = [completion (worlds state branch)] ∧
      (∀ target, ContextualEffectTreeLanguage.theory.Step
        (ContextualEffectTreeLanguage.request program state branch) target ↔
          target = completion (worlds state branch)) ∧
      (∀ world ∈ worlds state branch,
        FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules
          OpaqueRelatorScopedComputation.Common.context world.answer
          (subst OpaqueRelatorScopedComputation.Common.environment (.sigma ground identityFamily))) :=
  ⟨OpaqueRelatorScopedComputation.Common.source_judgment,
    backend_exact _ state branch (Nat.le_refl _), backend_step_iff state branch,
    worlds_admitted state branch⟩

/-- Reversing enumeration changes the first retained private state. -/
theorem worlds_not_reversed (state : Bool) (branch : BranchTrace) :
    worlds state branch ≠ (worlds state branch).reverse := by
  intro equal
  have states := congrArg (fun results => results.head?.map WorldResult.state) equal
  rw [worlds_shape] at states
  change some true = some false at states
  cases states

theorem reversed_completion_differs (state : Bool) (branch : BranchTrace) :
    completion (worlds state branch) ≠ completion (worlds state branch).reverse :=
  fun equal => worlds_not_reversed state branch (completion_injective equal)

theorem reversed_completion_rejected (state : Bool) (branch : BranchTrace) :
    ¬ ContextualEffectTreeLanguage.theory.Step
      (ContextualEffectTreeLanguage.request program state branch)
      (completion (worlds state branch).reverse) := by
  intro step
  exact reversed_completion_differs state branch ((backend_step_iff state branch _).mp step).symm

/-- The target cannot drop the losing occurrence while advertising the full
world-list observation. Selection is a separate public operation. -/
theorem missing_world_rejected (state : Bool) (branch : BranchTrace) :
    ¬ ContextualEffectTreeLanguage.theory.Step
      (ContextualEffectTreeLanguage.request program state branch)
      (completion ((worlds state branch).take 1)) := by
  intro step
  have equal := completion_injective ((backend_step_iff state branch _).mp step)
  have lengths := congrArg List.length equal
  rw [worlds_shape] at lengths
  change 1 = 2 at lengths
  cases lengths

/-- Fill the actual mixed variable with an existing HOL-list/wire payload. -/
def filledProgram (wire : NativeWireData.Wire) : Program Bool Pattern Pattern :=
  nativeProgram (Code.interpret handler (OpaqueRelatorScopedComputation.Common.filledEnvironment wire) source)

def filledWorlds (wire : NativeWireData.Wire) (state : Bool) (branch : BranchTrace) :
    List (WorldResult Bool (Tower.Tm 2) Nat) :=
  Code.worlds primitiveWorlds (OpaqueRelatorScopedComputation.Common.filledEnvironment wire) source state branch

theorem filledProgram_worlds (wire : NativeWireData.Wire) (state : Bool) (branch : BranchTrace) :
    runWorldsAt (filledProgram wire) state branch = (filledWorlds wire state branch).map nativeWorld := by
  rw [filledProgram, nativeProgram_worlds, Code.interpret_worlds handler primitiveWorlds handler_realizes]
  rfl

theorem filledWorlds_admitted (wire : NativeWireData.Wire) (state : Bool) (branch : BranchTrace)
    (world : WorldResult Bool (Tower.Tm 2) Nat) (returned : world ∈ filledWorlds wire state branch) :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules NativeExamples.context world.answer
      (subst (OpaqueRelatorScopedComputation.Common.filledEnvironment wire) (.sigma ground identityFamily)) := by
  apply OpaqueRelatorScopedComputation.Common.filled_source_results wire
  rw [Code.interpret_worlds handler primitiveWorlds handler_realizes]
  exact returned

theorem filled_backend_exact (wire : NativeWireData.Wire) (fuel : Nat) (state : Bool) (branch : BranchTrace)
    (adequate : ContextualEffectTreeLanguage.depth (filledProgram wire) ≤ fuel) :
    ContextualEffectTreeLanguage.execute fuel
        (ContextualEffectTreeLanguage.request (filledProgram wire) state branch) =
      [completion (filledWorlds wire state branch)] := by
  rw [ContextualEffectTreeLanguage.executor_exact fuel _ state branch adequate, filledProgram_worlds]
  rfl

theorem filled_backend_step_iff (wire : NativeWireData.Wire)
    (state : Bool) (branch : BranchTrace) (target : Pattern) :
    ContextualEffectTreeLanguage.theory.Step
        (ContextualEffectTreeLanguage.request (filledProgram wire) state branch) target ↔
      target = completion (filledWorlds wire state branch) := by
  rw [ContextualEffectTreeLanguage.theory_step_request_iff, filledProgram_worlds]
  rfl

/-- The filled program is unchanged when its two native substitutions are
performed separately, including the lifted dependent sequence binder. -/
theorem filledProgram_substitution (wire : NativeWireData.Wire) :
    nativeProgram (Code.interpret handler (OpaqueRelatorScopedComputation.Common.fillPayload wire)
      (source.substitute OpaqueRelatorScopedComputation.Common.environment)) = filledProgram wire := by
  rw [Code.interpret_substitute]
  rfl

/-- The actual first result contains an older free variable. Its payload is
not accepted as a closed term, even though it has a genuine scope-two type. -/
theorem first_filled_world_not_closed (wire : NativeWireData.Wire) (state : Bool) (branch : BranchTrace) :
    ((filledWorlds wire state branch).head?.map nativeWorld).bind
      (decodePayloadWorld DeclarationAwarePatternCodec.towerHeadCodec natCodec 0) = none :=
  rfl

end Common

namespace Controls

open NativeExamples

def wrongWorld : WorldResult Bool (Tower.Tm 2) Nat :=
  { branch := [], answer := .refl older, state := false, intents := [40] }

/-- This is the existing altered handler at an actual admitted call, not an
extra target transition added to the backend. -/
def wrongProgram : Program Bool (Tower.Tm 2) Nat :=
  Code.interpret ImplementationStudy.Native.misindexed.handler ids (.call .reflexivity newer)

/-- Exact serialization and exact execution cannot qualify an incorrect
dependent result. All judgments below use the same common native rules. -/
theorem exact_backend_does_not_supply_admission :
    decodeWorlds? 2 (encodeWorlds [wrongWorld]) = some [wrongWorld] ∧
      ContextualEffectTreeLanguage.theory.Step (request wrongProgram false []) (completion [wrongWorld]) ∧
      ¬ FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules context
        wrongWorld.answer (signature.result .reflexivity newer) := by
  refine ⟨decodeWorlds?_encodeWorlds _, (native_complete_iff _ _ _ _).mpr rfl, ?_⟩
  intro admitted
  exact OpaqueRelatorScopedComputation.wrong_selected_index_not_admitted
    HOLNativeRelatorCompatibility.opacity admitted.typing

/-- A different primitive specification cannot authorize the altered
handler's actual backend output merely because it preserves native results. -/
theorem unrealized_worlds_rejected :
    ¬ ContextualEffectTreeLanguage.theory.Step (request wrongProgram false [])
      (completion (primitiveWorlds .reflexivity newer false [])) := by
  intro step
  have equal := (native_complete_iff _ _ _ _).mp step
  have answers := congrArg (fun worlds => worlds.map WorldResult.answer) equal
  change ([.refl newer] : List (Tower.Tm 2)) = [.refl older] at answers
  cases answers

end Controls

#print axioms mapWorld
#print axioms mapProgram
#print axioms mapProgram_worlds
#print axioms mapWorld_injective
#print axioms natCodec
#print axioms payloadWorld
#print axioms payloadWorld_injective
#print axioms encodePayloadWorlds
#print axioms encodePayloadWorlds_injective
#print axioms payloadCompletion
#print axioms payloadCompletion_injective
#print axioms decode_intents_encode
#print axioms decodePayloadWorld
#print axioms decodePayloadWorld_payloadWorld
#print axioms payloadProgram
#print axioms payloadProgram_worlds
#print axioms payloadProgram_substitute
#print axioms payloadProgram_results
#print axioms compile
#print axioms compile_substitute
#print axioms qualified_executor_exact
#print axioms qualified_executor_no_invention
#print axioms qualified_step_iff
#print axioms qualified_step_results
#print axioms nativeProgram
#print axioms nativeWorld
#print axioms nativeProgram_worlds
#print axioms nativeWorld_injective
#print axioms encodeWorlds
#print axioms encodeWorlds_injective
#print axioms completion
#print axioms completion_injective
#print axioms request
#print axioms native_step_iff
#print axioms native_complete_iff
#print axioms native_executor_exact
#print axioms native_executor_no_invention
#print axioms decodeWorlds?
#print axioms decodeWorlds?_encodeWorlds
#print axioms Common.program
#print axioms Common.worlds
#print axioms Common.program_worlds
#print axioms Common.worlds_shape
#print axioms Common.worlds_admitted
#print axioms Common.backend_exact
#print axioms Common.backend_step_iff
#print axioms Common.backend_contract
#print axioms Common.worlds_not_reversed
#print axioms Common.reversed_completion_differs
#print axioms Common.reversed_completion_rejected
#print axioms Common.missing_world_rejected
#print axioms Common.filledProgram
#print axioms Common.filledWorlds
#print axioms Common.filledProgram_worlds
#print axioms Common.filledWorlds_admitted
#print axioms Common.filled_backend_exact
#print axioms Common.filled_backend_step_iff
#print axioms Common.filledProgram_substitution
#print axioms Common.first_filled_world_not_closed
#print axioms Controls.wrongWorld
#print axioms Controls.wrongProgram
#print axioms Controls.exact_backend_does_not_supply_admission
#print axioms Controls.unrealized_worlds_rejected

end ScopedComputationEffectTree
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
