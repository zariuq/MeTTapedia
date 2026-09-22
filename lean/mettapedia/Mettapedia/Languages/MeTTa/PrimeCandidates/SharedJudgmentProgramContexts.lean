import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPublicContext
import Mettapedia.GSLT.Core.PolicyFamilyContextClosure

/-!
# Public computation contexts and retained worlds

Equality of the complete ordered worlds is stable under the actual shared
service program's substitution, both sequencing forms, and choice. The
quantification over environments and initial worlds is essential: a
continuation runs with the value and state actually returned by its prefix.
Existing backend adequacy transports this congruence to completed runs.

This is a scoped computational observation, not code equality, definitional
conversion, equal evaluation costs, or a claim about arbitrary reflection,
thunk capture, sharing or resampling. The latter need their own context
operations and consumers. Native admission remains independently required.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProgramContexts

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation SharedJudgmentFragment SharedJudgmentServicePrograms
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ServiceResumption

variable {assembly : Assembly} {n m k : Nat}

/-- The actual submitted program runs at every native environment and
initial world. Replies, stopped outcomes, effects and order are retained. -/
def WorldEquivalent (assembly : Assembly) (first second : Code n) : Prop :=
  ∀ (m : Nat) (environment : Sub Tower.Head n m) (state : Bool) (branch : BranchTrace),
    Code.worlds assembly environment first state branch =
      Code.worlds assembly environment second state branch

theorem worlds_substitute (execution : ExecutionQualified assembly)
    (later : Sub Tower.Head m k) (earlier : Sub Tower.Head n m)
    (code : Code n) (state : Bool) (branch : BranchTrace) :
    Code.worlds assembly later (code.substitute earlier) state branch =
      Code.worlds assembly (subComp later earlier) code state branch := by
  rw [← Code.interpret_worlds assembly execution,
    ← Code.interpret_worlds assembly execution]
  simp only [Code.run, Code.interpret_substitute]

theorem WorldEquivalent.substitute (execution : ExecutionQualified assembly)
    {first second : Code n} (same : WorldEquivalent assembly first second)
    (environment : Sub Tower.Head n m) :
    WorldEquivalent assembly (first.substitute environment) (second.substitute environment) := by
  intro k later state branch
  rw [worlds_substitute execution, worlds_substitute execution]
  exact same k _ state branch

theorem WorldEquivalent.sequence {first second : Code n} {left right : Code (n + 1)}
    (firstSame : WorldEquivalent assembly first second)
    (body : WorldEquivalent assembly left right) :
    WorldEquivalent assembly (.sequence first left) (.sequence second right) := by
  intro m environment state branch
  simp only [Code.worlds, firstSame m environment state branch]
  apply List.flatMap_congr
  intro prior _
  cases prior.world.answer with
  | value value =>
      dsimp only
      rw [body m (consSub value environment) prior.world.state prior.world.branch]
  | stopped reply => rfl

theorem WorldEquivalent.sequenceSigma {first second : Code n} {left right : Code (n + 1)}
    (firstSame : WorldEquivalent assembly first second)
    (body : WorldEquivalent assembly left right) :
    WorldEquivalent assembly (.sequenceSigma first left) (.sequenceSigma second right) := by
  intro m environment state branch
  simp only [Code.worlds, firstSame m environment state branch]
  apply List.flatMap_congr
  intro prior _
  cases prior.world.answer with
  | value value =>
      dsimp only
      rw [body m (consSub value environment) prior.world.state prior.world.branch]
  | stopped reply => rfl

theorem WorldEquivalent.choose {first second left right : Code n}
    (firstSame : WorldEquivalent assembly first second)
    (secondSame : WorldEquivalent assembly left right) :
    WorldEquivalent assembly (.choose first left) (.choose second right) := by
  intro m environment state branch
  simp only [Code.worlds, firstSame m environment state (false :: branch),
    secondSame m environment state (true :: branch)]

theorem WorldEquivalent.refl (code : Code n) : WorldEquivalent assembly code code :=
  fun _ _ _ _ => rfl

/-- These operations build actual source contexts. Sequencing-body contexts
remove one source variable; substitution can change the native scope. -/
inductive Operation : Nat → Nat → Type where
  | substitute {n m : Nat} (environment : Sub Tower.Head n m) : Operation n m
  | sequenceFirst {n : Nat} (body : Code (n + 1)) : Operation n n
  | sequenceBody {n : Nat} (first : Code n) : Operation (n + 1) n
  | sigmaFirst {n : Nat} (body : Code (n + 1)) : Operation n n
  | sigmaBody {n : Nat} (first : Code n) : Operation (n + 1) n
  | chooseLeft {n : Nat} (right : Code n) : Operation n n
  | chooseRight {n : Nat} (left : Code n) : Operation n n

local instance : Quiver Nat where
  Hom := Operation

def execute {n m : Nat} : Operation n m → Code n → Code m
  | .substitute environment, code => code.substitute environment
  | .sequenceFirst body, code => .sequence code body
  | .sequenceBody first, code => .sequence first code
  | .sigmaFirst body, code => .sequenceSigma code body
  | .sigmaBody first, code => .sequenceSigma first code
  | .chooseLeft right, code => .choose code right
  | .chooseRight left, code => .choose left code

theorem execute_preserves (execution : ExecutionQualified assembly)
    (operation : Operation n m) {first second : Code n}
    (same : WorldEquivalent assembly first second) :
    WorldEquivalent assembly (execute operation first) (execute operation second) := by
  cases operation with
  | substitute environment => exact same.substitute execution environment
  | sequenceFirst body => exact same.sequence (.refl body)
  | sequenceBody initial =>
      exact WorldEquivalent.sequence (assembly := assembly) (n := m) (.refl initial) same
  | sigmaFirst body => exact same.sequenceSigma (.refl body)
  | sigmaBody initial =>
      exact WorldEquivalent.sequenceSigma (assembly := assembly) (n := m) (.refl initial) same
  | chooseLeft right => exact same.choose (.refl right)
  | chooseRight left => exact (WorldEquivalent.refl left).choose same

structure EvaluationAt (n : Nat) where
  scope : Nat
  environment : Sub Tower.Head n scope
  state : Bool
  branch : BranchTrace

def worldFamily (assembly : Assembly) (n : Nat) : PolicyFamily (Code n) where
  Policy := EvaluationAt n
  Result input := List (SharedJudgmentServiceProgramBackend.Output input.scope)
  decide input code := Code.worlds assembly input.environment code input.state input.branch

theorem worldFamily_equivalent_iff (first second : Code n) :
    (worldFamily assembly n).PolicyEquivalent first second ↔
      WorldEquivalent assembly first second := by
  constructor
  · intro same m environment state branch
    exact same ⟨m, environment, state, branch⟩
  · rintro same ⟨m, environment, state, branch⟩
    exact same m environment state branch

/-- Existing operation-context closure, specialized to this actual syntax
and these consumers. This introduces no new operational interpreter. -/
def contextualFamily (assembly : Assembly) (n : Nat) : PolicyFamily (Code n) :=
  PolicyFamily.ContextClosure.family execute (worldFamily assembly) n

/-- Complete-world observations already close under this computational
context inventory. This says nothing about a newly added code inspector. -/
theorem contextual_equivalent_iff (execution : ExecutionQualified assembly)
    (first second : Code n) :
    (contextualFamily assembly n).PolicyEquivalent first second ↔
      WorldEquivalent assembly first second := by
  constructor
  · intro same
    exact (worldFamily_equivalent_iff first second).mp
      (PolicyFamily.ContextClosure.preserves_base (@execute) (worldFamily assembly) same)
  · intro same
    exact PolicyFamily.ContextClosure.greatest (@execute) (worldFamily assembly)
      (fun _ => WorldEquivalent assembly)
      (fun _ _ _ related => (worldFamily_equivalent_iff _ _).mpr related)
      (fun {_ _} operation {_ _} related => execute_preserves execution operation related) same

/-- The independently authored backend completes with the same exact
output in every context from the inventory, in both directions. -/
theorem contextual_completion_iff (execution : ExecutionQualified assembly)
    {first second : Code n} (same : WorldEquivalent assembly first second)
    (path : Quiver.Path n m) (environment : Sub Tower.Head m k)
    (state : Bool) (branch : BranchTrace)
    (outputs : List (SharedJudgmentServiceProgramBackend.Output k)) :
    SharedJudgmentServiceProgramBackend.Reaches assembly
        (SharedJudgmentServiceProgramBackend.start environment
          (PolicyFamily.ContextClosure.runPath execute path first) state branch)
        (.completed outputs) ↔
      SharedJudgmentServiceProgramBackend.Reaches assembly
        (SharedJudgmentServiceProgramBackend.start environment
          (PolicyFamily.ContextClosure.runPath execute path second) state branch)
        (.completed outputs) := by
  rw [SharedJudgmentServiceProgramBackend.completion_worlds_iff assembly execution,
    SharedJudgmentServiceProgramBackend.completion_worlds_iff assembly execution]
  have contextual := (contextual_equivalent_iff execution first second).mpr same
  have observed := contextual ⟨m, path, ⟨k, environment, state, branch⟩⟩
  change Code.worlds assembly environment
      (PolicyFamily.ContextClosure.runPath execute path first) state branch =
    Code.worlds assembly environment
      (PolicyFamily.ContextClosure.runPath execute path second) state branch at observed
  rw [observed]

namespace Controls

/-- A real administrative sequence can disappear under computational use
without changing the source term retained by a reflection consumer. -/
def direct : Code 1 := .native (.returnValue (.var 0))
def detour : Code 1 := .sequence direct (.native (.returnValue (.var 0)))

theorem direct_detour_equivalent : WorldEquivalent common direct detour := by
  intro m environment state branch
  simp only [direct, detour, Code.worlds, ScopedComputation.Code.worlds,
    subst, consSub_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_nil, Result.prepend]

theorem direct_detour_code_distinct : direct ≠ detour := by
  intro same
  cases same

theorem computational_contexts_keep_detour_hidden :
    (contextualFamily common 1).PolicyEquivalent direct detour :=
  (contextual_equivalent_iff common_execution direct detour).mpr direct_detour_equivalent

theorem complete_worlds_cannot_recover_code :
    ¬ NonFactorization.Factors (worldFamily common 1).vector (id : Code 1 → Code 1) := by
  intro factors
  have same : (worldFamily common 1).vector direct = (worldFamily common 1).vector detour := by
    funext input
    exact (worldFamily_equivalent_iff direct detour).mpr direct_detour_equivalent input
  exact direct_detour_code_distinct (factors.constantOnFibers direct detour same)

def input (state : Bool) : SharedJudgmentPublicContext.Input 2 2 where
  sourceContext := ScopedComputation.NativeExamples.context
  code := .native (.returnValue (.var 0))
  resultType := ScopedComputation.NativeExamples.ground
  environment := ids
  initialState := state
  initialBranch := []

def appendReflexivity (input : SharedJudgmentPublicContext.Input 2 2) :
    SharedJudgmentPublicContext.Input 2 2 :=
  { input with
    code := .sequenceSigma input.code (.native (.call .reflexivity (.var 0)))
    resultType := .sigma input.resultType
      (.id (rename wk input.resultType) (.var 0) (.var 0)) }

theorem input_admitted (state : Bool) :
    (input state).Admitted common ScopedComputation.NativeExamples.context := by
  have contextFormed := OpaqueRelatorScopedComputation.context_formed common.declarations
  refine ⟨.native ⟨contextFormed, .returnValue (.var 0)⟩, contextFormed, ?_⟩
  intro index
  simpa only [input, ids, subst_ids] using
    (FormationSensitive.Typing.var (R := common.rules)
      (Γ := ScopedComputation.NativeExamples.context) index)

theorem continuation_admitted (state : Bool) :
    (appendReflexivity (input state)).Admitted common
      ScopedComputation.NativeExamples.context := by
  have contextFormed := (input_admitted state).2.1
  refine ⟨.sequenceSigma ?_ (.sort (.max Tower.zero Tower.zero)) (input_admitted state).1 ?_,
    contextFormed, (input_admitted state).2.2⟩
  · exact .sigmaForm (.headType .legacyGround) (.sort Tower.zero)
      (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
      (.sort Tower.zero) (.sorts Tower.zero Tower.zero)
  · exact .native ⟨.snoc contextFormed (.headType .legacyGround) (.sort Tower.zero),
      .call (OpaqueRelatorScopedComputation.operation_formation common.declarations .reflexivity)
        (.var 0)⟩

def answers (input : SharedJudgmentPublicContext.Input 2 2) :=
  (input.run common).map (fun output => output.world.answer)

def futureIntents (input : SharedJudgmentPublicContext.Input 2 2) :=
  ((appendReflexivity input).run common).map (fun output => output.world.intents)

theorem current_answers_same : answers (input false) = answers (input true) := by
  unfold answers SharedJudgmentPublicContext.Input.run
  rw [Code.interpret_worlds common common_execution, Code.interpret_worlds common common_execution]
  rfl

theorem future_effects_differ : futureIntents (input false) ≠ futureIntents (input true) := by
  unfold futureIntents SharedJudgmentPublicContext.Input.run
  rw [Code.interpret_worlds common common_execution, Code.interpret_worlds common common_execution]
  decide

/-- Present answers do not determine the effects of an admitted continuation
which consults the retained state. This is a failure of a particular view,
not a requirement that every consumer retain all state forever. -/
theorem answer_only_cannot_support_continuation :
    ¬ NonFactorization.Factors answers futureIntents := by
  intro factors
  exact future_effects_differ (factors.constantOnFibers _ _ current_answers_same)

end Controls

#print axioms contextual_equivalent_iff
#print axioms contextual_completion_iff
#print axioms Controls.computational_contexts_keep_detour_hidden
#print axioms Controls.complete_worlds_cannot_recover_code
#print axioms Controls.continuation_admitted
#print axioms Controls.answer_only_cannot_support_continuation

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentProgramContexts
