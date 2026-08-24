import Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds

/-!
# Gradual precision for native parallel rho worlds

A separation certificate refines one already-authorized rho branch with a
native scheduling capability.  It does not replace the branch's target and it
does not choose between other nondeterministic branches.

This module makes that gradual boundary explicit.  Every certified finite
family has a proof-relevant raw erasure, certification is one precision step,
and deoptimization recovers the raw step.  Pointwise precision preserves the
complete ordered target-occurrence list.  The richer observation may gain a
native `WorkSpan`; the target-only observation cannot detect that gain.

The contested communication control proves the complementary boundary: two
coexisting rho alternatives with different targets are not precision
refinements of one another.  Native parallel precision is therefore an
intra-world capability, never a nondeterministic branch-selection rule.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee

open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## One certified world as a gradual refinement of its raw rho step -/

/-- Forget only the native scheduling capability of a certified family.  The
result retains the exact receipt, target, and proof-relevant rho step. -/
def rawOfCertified {Ground : Type} {source target : CostConfig Ground}
    (execution : AnyCertifiedFamilyExecution Ground source target) :
    RawBranchWorld source :=
  let separation := execution.2.separation
  let step : ParallelCostStep source separation.receipt target :=
    Eq.mp
      (congrArg
        (fun final => ParallelCostStep source separation.receipt final)
        execution.2.target_eq)
      separation.parallelStep
  ⟨separation.receipt, target, ⟨step⟩⟩

@[simp] theorem rawOfCertified_target {Ground : Type}
    {source target : CostConfig Ground}
    (execution : AnyCertifiedFamilyExecution Ground source target) :
    (rawOfCertified execution).2.1 = target := by
  rfl

/-- Proof-relevant gradual precision on one execution world.  Reflexivity
retains ordinary worlds.  The only proper precision step attaches the exact
finite-family certificate to its own raw rho erasure. -/
inductive WorldRefines {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorld Ground source → ExecutionWorld Ground source → Type where
  | refl (world : ExecutionWorld Ground source) : WorldRefines world world
  | certify {target : CostConfig Ground}
      (execution : AnyCertifiedFamilyExecution Ground source target) :
      WorldRefines (.raw (rawOfCertified execution)) (.parallel execution)

namespace WorldRefines

/-- Precision steps compose.  There is deliberately no constructor that
turns one raw alternative into another. -/
def trans {Ground : Type} {source : CostConfig Ground}
    {first middle last : ExecutionWorld Ground source}
    (earlier : WorldRefines first middle)
    (later : WorldRefines middle last) : WorldRefines first last := by
  cases later with
  | refl => exact earlier
  | certify execution =>
      cases earlier with
      | refl => exact .certify execution

/-- Native precision cannot change the visible rho target. -/
theorem target_eq {Ground : Type} {source : CostConfig Ground}
    {coarse refined : ExecutionWorld Ground source}
    (precision : WorldRefines coarse refined) :
    coarse.target = refined.target := by
  cases precision with
  | refl => rfl
  | certify execution =>
      exact rawOfCertified_target execution

/-- Realizing both sides preserves the same visible target equality. -/
theorem realized_target_eq {Ground : Type} {source : CostConfig Ground}
    {coarse refined : ExecutionWorld Ground source}
    (precision : WorldRefines coarse refined) :
    (realize coarse).target = (realize refined).target := by
  simpa only [realize_target] using precision.target_eq

end WorldRefines

/-! ## Deoptimization -/

/-- The exact raw rho branch underlying either a raw or certified execution
world. -/
def rawProjection {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorld Ground source → RawBranchWorld source
  | .raw world => world
  | .parallel execution => rawOfCertified execution

/-- Remove native scheduling evidence while retaining the exact raw rho
branch.  Raw worlds are unchanged. -/
def deopt {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorld Ground source → ExecutionWorld Ground source
  | world => .raw (rawProjection world)

@[simp] theorem rawProjection_deopt {Ground : Type}
    {source : CostConfig Ground} (world : ExecutionWorld Ground source) :
    rawProjection (deopt world) = rawProjection world := by
  cases world <;> rfl

/-- Every world is a refinement of its deoptimized raw form. -/
def deopt_refines {Ground : Type} {source : CostConfig Ground}
    (world : ExecutionWorld Ground source) : WorldRefines (deopt world) world := by
  cases world with
  | raw rawWorld => exact .refl (.raw rawWorld)
  | parallel execution => exact .certify execution

@[simp] theorem deopt_idempotent {Ground : Type}
    {source : CostConfig Ground} (world : ExecutionWorld Ground source) :
    deopt (deopt world) = deopt world := by
  cases world <;> rfl

@[simp] theorem deopt_target {Ground : Type} {source : CostConfig Ground}
    (world : ExecutionWorld Ground source) :
    (deopt world).target = world.target :=
  (deopt_refines world).target_eq

/-- Deoptimization changes neither the result seen before realization nor the
result seen after realization. -/
theorem deopt_realized_target {Ground : Type}
    {source : CostConfig Ground} (world : ExecutionWorld Ground source) :
    (realize (deopt world)).target = (realize world).target :=
  (deopt_refines world).realized_target_eq

/-! ## Ordered families of nondeterministic worlds -/

/-- Pointwise precision for an ordered occurrence family.  This is
Type-valued so each certification occurrence remains available as evidence. -/
inductive WorldsRefine {Ground : Type} {source : CostConfig Ground} :
    ExecutionWorlds Ground source → ExecutionWorlds Ground source → Type where
  | nil : WorldsRefine [] []
  | cons {coarseHead refinedHead : ExecutionWorld Ground source}
      {coarseTail refinedTail : ExecutionWorlds Ground source}
      (head : WorldRefines coarseHead refinedHead)
      (tail : WorldsRefine coarseTail refinedTail) :
      WorldsRefine (coarseHead :: coarseTail) (refinedHead :: refinedTail)

namespace WorldsRefine

@[simp] theorem length_eq {Ground : Type} {source : CostConfig Ground}
    {coarse refined : ExecutionWorlds Ground source}
    (precision : WorldsRefine coarse refined) :
    coarse.length = refined.length := by
  induction precision with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/-- Pointwise precision preserves the complete ordered target-occurrence
list, not merely its set or cardinality. -/
theorem targets_eq {Ground : Type} {source : CostConfig Ground}
    {coarse refined : ExecutionWorlds Ground source}
    (precision : WorldsRefine coarse refined) :
    coarse.map ExecutionWorld.target = refined.map ExecutionWorld.target := by
  induction precision with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons]
      rw [head.target_eq, inductionHypothesis]

/-- The same ordered target equality survives native realization. -/
theorem realized_targets_eq {Ground : Type} {source : CostConfig Ground}
    {coarse refined : ExecutionWorlds Ground source}
    (precision : WorldsRefine coarse refined) :
    (realizeWorlds coarse).map RealizedWorld.target =
      (realizeWorlds refined).map RealizedWorld.target := by
  rw [realizeWorlds_targets, realizeWorlds_targets]
  exact precision.targets_eq

end WorldsRefine

def deoptWorlds {Ground : Type} {source : CostConfig Ground}
    (worlds : ExecutionWorlds Ground source) : ExecutionWorlds Ground source :=
  worlds.map deopt

/-- Deoptimizing a nondeterministic family is a pointwise precision
predecessor with exactly the same occurrence shape. -/
def deoptWorlds_refines {Ground : Type} {source : CostConfig Ground}
    (worlds : ExecutionWorlds Ground source) :
    WorldsRefine (deoptWorlds worlds) worlds := by
  induction worlds with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (deopt_refines head) inductionHypothesis

@[simp] theorem deoptWorlds_length {Ground : Type}
    {source : CostConfig Ground} (worlds : ExecutionWorlds Ground source) :
    (deoptWorlds worlds).length = worlds.length :=
  (deoptWorlds_refines worlds).length_eq

theorem deoptWorlds_targets {Ground : Type}
    {source : CostConfig Ground} (worlds : ExecutionWorlds Ground source) :
    (deoptWorlds worlds).map ExecutionWorld.target =
      worlds.map ExecutionWorld.target :=
  (deoptWorlds_refines worlds).targets_eq

/-! ## Positive and negative controls -/

namespace Examples.Separated

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNIKAdmission.Examples.Separated
open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples.Separated

theorem rawOfCertified_pairExecution :
    rawOfCertified pairExecution =
      internalBranchWorld oneColourFamily.parallelStep PUnit.unit := by
  simp [rawOfCertified, pairExecution, internalBranchWorld]

/-- The certified two-event family is a proper precision refinement of its
own raw rho step. -/
def rawPairWorld_refines_world : WorldRefines rawPairWorld world := by
  change WorldRefines
    (ExecutionWorld.raw
      (internalBranchWorld oneColourFamily.parallelStep PUnit.unit))
    (ExecutionWorld.parallel pairExecution)
  rw [← rawOfCertified_pairExecution]
  exact .certify pairExecution

@[simp] theorem deopt_world_eq_rawPairWorld :
    deopt world = rawPairWorld := by
  change ExecutionWorld.raw (rawOfCertified pairExecution) =
    ExecutionWorld.raw
      (internalBranchWorld oneColourFamily.parallelStep PUnit.unit)
  rw [rawOfCertified_pairExecution]

/-- Precision preserves the visible target while adding native scheduling
information to the richer observation. -/
theorem target_unchanged_but_native_schedule_added :
    rawPairWorld.target = world.target ∧
      rawPairWorld.value ≠ world.value := by
  constructor
  · exact rawPairWorld_refines_world.target_eq
  · intro same
    apply raw_and_certified_values_differ
    rw [same]

/-- A relevant revision change prevents activation of the retained native
realizer, but the exact raw rho erasure remains constructible. -/
theorem stale_admission_preserves_raw_deoptimization :
    ¬ admission.Active true ∧
      Nonempty (ExecutionWorld Ground source) := by
  constructor
  · rintro ⟨current⟩
    have changed := current ()
    simp [exampleDependencies] at changed
  · exact ⟨deopt world⟩

end Examples.Separated

namespace Examples.Contested

open Mettapedia.Languages.MeTTa.Prime.NativeParallelNondeterministicWorlds.Examples.Contested

@[simp] theorem deopt_contested_worlds : deoptWorlds worlds = worlds := rfl

/-- Coexistence is not precision: the two legal communications have
different targets, so neither can be obtained by merely attaching a native
parallel certificate to the other. -/
theorem alice_not_refines_competitor :
    ¬ Nonempty (WorldRefines alice competitor) := by
  rintro ⟨precision⟩
  exact realization_preserves_both_contested_worlds.2
    precision.realized_target_eq

theorem competitor_not_refines_alice :
    ¬ Nonempty (WorldRefines competitor alice) := by
  rintro ⟨precision⟩
  exact realization_preserves_both_contested_worlds.2
    precision.realized_target_eq.symm

/-- Deoptimization leaves both contested occurrences in place; their lack of
joint parallel authority is unchanged. -/
theorem deoptimization_preserves_contested_noncollapse :
    (deoptWorlds worlds).length = 2 ∧
      (deopt alice).target ≠ (deopt competitor).target ∧
      ¬ Nonempty
        (Σ target : CostConfig
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.ExampleGround,
          CertifiedFamilyExecution
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.ExampleGround
            [Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.aliceEvent,
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.aliceCompetitor]
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples.contestedSource
            target) := by
  refine ⟨rfl, ?_, alternatives_do_not_mint_joint_parallelism.2⟩
  intro same
  have original : alice.target = competitor.target :=
    (deopt_target alice).symm.trans (same.trans (deopt_target competitor))
  exact realization_preserves_both_contested_worlds.2
    (by simpa only [realize_target] using original)

end Examples.Contested

#print axioms rawOfCertified_target
#print axioms WorldRefines.trans
#print axioms WorldRefines.target_eq
#print axioms deopt_refines
#print axioms WorldsRefine.targets_eq
#print axioms deoptWorlds_refines
#print axioms Examples.Separated.target_unchanged_but_native_schedule_added
#print axioms Examples.Separated.stale_admission_preserves_raw_deoptimization
#print axioms Examples.Contested.alice_not_refines_competitor
#print axioms Examples.Contested.deoptimization_preserves_contested_noncollapse

end Mettapedia.Languages.MeTTa.Prime.NativeParallelGradualGuarantee
