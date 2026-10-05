import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadbackStep
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInitialRuntime
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Arbitrary concrete rho prefixes read back to scoped unary pi

Related states use the existing source restriction telescope, actual core
headers and preserved occurrence inventory. Original source-name positions
retain their exact allocated names. The target is the same authored rho
semantics over the declared free infrastructure names. Every supplied target
firing, including changes of sorted equation representative, reads back as
zero or one actual source communication at its supplied final endpoint.

This is a backward execution theorem with a finite administrative-work bound.
Forward execution from every partially initialized related phase, reflection
of infinite source computation, and quotation-observer adequacy are separate
contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive
open RhoUnaryInventory ScopedActiveFrontier RhoUnaryCredit
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation RhoEncodingTyping

abbrev Target := ParameterizedRewriteSystem.theory rhoAtomicNameContext
abbrev TargetProcess := ParameterizedRewriteSystem.Process rhoAtomicNameContext

/-- Actual runtime formation retains the declared free infrastructure names. -/
def runtimeProcess (code : Code 0) (seed : Nat) : TargetProcess := by
  refine ⟨runtime code seed, (ParameterizedRewriteSystem.process_iff _ _).mpr ⟨?_, ?_⟩⟩
  · exact .parallel (.cons code.typed
      (.cons (idle_typed allocatorSelf allocatorRequest (allocationHandler allocatorState))
        (.cons (.output allocatorState.typed (seedCode_typed rhoAtomicNameContext seed)) .nil)))
  · simpa [runtime, server, stateToken, RhoScopedServers.parallel, send,
      binderSafeAt, binderSafeListAt, code.safe, allocatorState.safe, seedCode_safe] using
      idle_safe allocatorSelf allocatorRequest (allocationHandler allocatorState)

/-- Only newly opened private source binders change the context. The runtime
world, activity incidence and source/target observations are independent data. -/
structure Witness {Γ : Ctx sig} (initialWorld : SeedWorld Γ)
    (origin : Proc Γ) (current : TargetProcess) where
  context : Ctx sig
  scope : Scope Γ context
  world : SeedWorld context
  activities : List (Activity context)
  inventory : Inventory world activities
  names : ∀ name, world.index (scope.inclusion .nm name) = initialWorld.index name
  cursor : initialWorld.available ≤ world.available
  source : StructuralEq origin (scope.close (RhoUnaryActive.source activities))
  endpoint : Canonical.canonicalize current.1 = Canonical.canonicalize (actual world.world activities)

def Related {Γ : Ctx sig} (initialWorld : SeedWorld Γ)
    (origin : Proc Γ) (current : TargetProcess) : Prop :=
  Nonempty (Witness initialWorld origin current)

def Witness.credit {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (witness : Witness initialWorld origin current) : Nat :=
  total witness.activities

/-- One supplied actual firing carries its activation charge and preserved
representation. Charge zero identifies implementation work exactly. -/
structure OneResult {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    (next : TargetProcess) where
  after : Proc Γ
  witness : Witness initialWorld after next
  charge : Nat
  status : (charge = 0 ∧ after = origin) ∨
    (0 < charge ∧ (operationalTheory Γ).Step origin after)
  balance : witness.credit + 1 = before.credit + charge

/-- Inclusion into a concatenated restriction telescope keeps the same
intrinsic variable in each intermediate source context. -/
theorem _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier.Scope.inclusion_append :
    ∀ {Γ Δ Θ : Ctx sig} (first : Scope Γ Δ) (second : Scope Δ Θ)
      (sort : Srt) (name : Var Γ sort),
      (first.append second).inclusion sort name = second.inclusion sort (first.inclusion sort name)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .bind rest, later, sort, name => rest.inclusion_append later sort (.succ name)

/-- Closing the supplied phase image composes its real scope telescope and
keeps all earlier public names at their original allocated addresses. -/
def Witness.afterResult {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (before : Witness initialWorld origin current)
    {target : Pattern} (result : RhoUnaryReadbackStep.Result before.world before.activities target)
    (after : Proc Γ) (next : TargetProcess)
    (sourceEq : StructuralEq after (before.scope.close
      (result.scope.close (RhoUnaryActive.source result.activities))))
    (targetEq : StructuralCongruence next.1 target) : Witness initialWorld after next where
  context := result.context
  scope := before.scope.append result.scope
  world := result.world
  activities := result.activities
  inventory := result.inventory
  names := by
    intro name
    rw [Scope.inclusion_append, result.names, before.names]
  cursor := before.cursor.trans result.cursor
  source := by
    rw [Scope.close_append]
    exact sourceEq
  endpoint := Canonical.canonicalize_eq_of_structuralCongruence
    (.trans _ _ _ targetEq result.endpoint)
    (rhoProcWellSorted_hashSetFree ((ParameterizedRewriteSystem.process_iff _ _).mp next.2).1)
    (rhoProcWellSorted_hashSetFree (parallel_typed (headers_typed result.world.world result.activities)))

private theorem scoped_step {Γ Δ : Ctx sig} (scope : Scope Γ Δ) {first second : Proc Δ}
    (step : StepModulo first second) : StepModulo (scope.close first) (scope.close second) := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact ⟨scope.close redex, scope.close contractum, scope.congr before,
    scope.step firing, scope.congr after⟩

private theorem source_step_precompose {Γ : Ctx sig} {before middle after : Proc Γ}
    (equal : StructuralEq before middle) (step : StepModulo middle after) : StepModulo before after := by
  obtain ⟨source, target, beforeEq, firing, afterEq⟩ := step
  exact ⟨source, target, .trans equal beforeEq, firing, afterEq⟩

/-- The literal supplied primitive target endpoint has a valid reflected
world, source readout and exact administrative credit law. -/
theorem readOne {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current next : TargetProcess}
    (beforeWitness : Witness initialWorld origin current) (step : Target.Step current next) :
    Nonempty (OneResult beforeWitness next) := by
  rcases beforeWitness with ⟨Δ, scope, world, activities, inventory, names, cursor, sourceEq, represented⟩
  obtain ⟨redex, contractum, before, firing, after⟩ := ParameterizedRewriteSystem.step_iff.mp step
  have redexFormation := (ParameterizedRewriteSystem.process_iff _ _).mp redex.2
  have redexImage : Canonical.canonicalize redex.1 = canonicalParallel (headers world.world activities) :=
    before.symm.trans represented
  obtain ⟨selected, suppliedEndpoint⟩ := representative_selection_of_step
    (headers_typed world.world activities) (headers_safe world.world activities)
    redexFormation.1 redexFormation.2 redexImage firing
  obtain ⟨result⟩ := RhoUnaryReadbackStep.selection world activities inventory selected
  have endImage : Canonical.canonicalize next.1 =
      Canonical.canonicalize (actual result.world.world result.activities) := by
    refine after.symm.trans (suppliedEndpoint.trans ?_)
    exact Canonical.canonicalize_eq_of_structuralCongruence result.endpoint
      (selected.contractum_hashSetFree (headers_typed world.world activities)
        (headers_safe world.world activities))
      (rhoProcWellSorted_hashSetFree (parallel_typed (headers_typed result.world.world result.activities)))
  have nextNames : ∀ name,
      result.world.index ((scope.append result.scope).inclusion .nm name) = initialWorld.index name := by
    intro name
    rw [Scope.inclusion_append, result.names, names]
  have nextCursor : initialWorld.available ≤ result.world.available := cursor.trans result.cursor
  have closedEq : (scope.append result.scope).close (source result.activities) =
      scope.close (result.scope.close (source result.activities)) := Scope.close_append _ _ _
  rcases result.status with ⟨zeroCharge, unchanged⟩ | ⟨positiveCharge, advanced⟩
  · have sourceAfter : StructuralEq origin ((scope.append result.scope).close (source result.activities)) := by
      rw [closedEq]
      exact .trans sourceEq (scope.congr unchanged)
    exact ⟨⟨origin,
      ⟨result.context, scope.append result.scope, result.world, result.activities,
        result.inventory, nextNames, nextCursor, sourceAfter, endImage⟩,
      result.charge, .inl ⟨zeroCharge, rfl⟩, result.credit⟩⟩
  · let final := (scope.append result.scope).close (source result.activities)
    have sourceStep : (operationalTheory Γ).Step origin final := by
      change StepModulo origin final
      dsimp only [final]
      rw [closedEq]
      exact source_step_precompose sourceEq (scoped_step scope advanced)
    exact ⟨⟨final,
      ⟨result.context, scope.append result.scope, result.world, result.activities,
        result.inventory, nextNames, nextCursor, .refl _, endImage⟩,
      result.charge, .inr ⟨positiveCharge, sourceStep⟩, result.credit⟩⟩

/-- Forgetting the exact credit law yields the same concrete zero/one-step
readback; it does not introduce a second implementation invariant. -/
theorem readStep {Γ : Ctx sig} (initialWorld : SeedWorld Γ)
    {origin : Proc Γ} {current next : TargetProcess}
    (related : Related initialWorld origin current) (step : Target.Step current next) :
    Related initialWorld origin next ∨
      ∃ after, (operationalTheory Γ).Step origin after ∧ Related initialWorld after next := by
  obtain ⟨before⟩ := related
  obtain ⟨result⟩ := readOne before step
  rcases result.status with ⟨_, unchanged⟩ | ⟨_, advanced⟩
  · exact .inl ⟨unchanged ▸ result.witness⟩
  · exact .inr ⟨result.after, advanced, ⟨result.witness⟩⟩

/-- The concrete compiler phases instantiate the shared arbitrary-prefix
readback interface over actual generated source and target semantics. -/
def comparison {Γ : Ctx sig} (initialWorld : SeedWorld Γ) :
    OperationalReadback (operationalTheory Γ) Target where
  related := Related initialWorld
  readStep := readStep initialWorld

/-- Every successful supplied compiler output starts this relation at its
actual shared allocator and exact cursor token. -/
theorem initial_related {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : SeedWorld Γ) (code : Code 0) (supplied : compile world.world process = some code) :
    Related world process (runtimeProcess code world.available) := by
  obtain ⟨activities, inventory, sourceEq, targetEq⟩ :=
    RhoUnaryInitialRuntime.initial_runtime guarded world code supplied
  refine ⟨⟨Γ, .nil, world, activities, inventory, fun _ => rfl, le_rfl, sourceEq, ?_⟩⟩
  exact Canonical.canonicalize_eq_of_structuralCongruence targetEq
    (rhoProcWellSorted_hashSetFree ((ParameterizedRewriteSystem.process_iff _ _).mp
      (runtimeProcess code world.available).2).1)
    (rhoProcWellSorted_hashSetFree (parallel_typed (headers_typed world.world activities)))

/-- Any independently supplied target prefix retains an actual source path
and the exact final target observation, including its private-name world. -/
theorem arbitrary_prefix {Γ : Ctx sig} (world : SeedWorld Γ)
    {origin : Proc Γ} {current final : TargetProcess} (related : Related world origin current)
    (path : ExecutionPath Target current final) :
    ∃ after, ∃ sourcePath : ExecutionPath (operationalTheory Γ) origin after,
      Related world after final ∧ sourcePath.length ≤ path.length :=
  (comparison world).reflectPath related path

/-- Whole-fragment supplied compilation and arbitrary target execution join. -/
theorem compiled_prefix {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : SeedWorld Γ) (code : Code 0) (supplied : compile world.world process = some code)
    {final : TargetProcess} (path : ExecutionPath Target (runtimeProcess code world.available) final) :
    ∃ after, ∃ sourcePath : ExecutionPath (operationalTheory Γ) process after,
      Related world after final ∧ sourcePath.length ≤ path.length :=
  arbitrary_prefix world (initial_related guarded world code supplied) path


/-- The source path, its positive activation charges, and the exact supplied
target endpoint remain together in one prefix certificate. -/
structure PrefixResult {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current final : TargetProcess} (before : Witness initialWorld origin current)
    (targetPath : ExecutionPath Target current final) where
  after : Proc Γ
  sourcePath : ExecutionPath (operationalTheory Γ) origin after
  witness : Witness initialWorld after final
  charges : List Nat
  chargedLength : charges.length = sourcePath.length
  positive : ∀ charge ∈ charges, 0 < charge
  length : sourcePath.length ≤ targetPath.length
  balance : witness.credit + targetPath.length = before.credit + charges.sum

/-- Each target step is inspected independently. The retained source route
and its activation charges concatenate along the actual target prefix. -/
theorem retainPrefix {Γ : Ctx sig} {initialWorld : SeedWorld Γ}
    {origin : Proc Γ} {current final : TargetProcess}
    (before : Witness initialWorld origin current) (path : ExecutionPath Target current final) :
    Nonempty (PrefixResult before path) := by
  induction path generalizing origin with
  | refl state =>
      exact ⟨⟨origin, .refl origin, before, [], rfl, by simp, le_rfl, rfl⟩⟩
  | cons first rest ih =>
      obtain ⟨after, afterWitness, charge, status, balance⟩ := readOne before first.down
      rcases status with ⟨zeroCharge, rfl⟩ | ⟨positiveCharge, advanced⟩
      · obtain ⟨remaining⟩ := ih afterWitness
        refine ⟨⟨remaining.after, remaining.sourcePath, remaining.witness, remaining.charges,
          remaining.chargedLength, remaining.positive, ?_, ?_⟩⟩
        · change remaining.sourcePath.length ≤ rest.length + 1
          have bounded := remaining.length
          change remaining.sourcePath.length ≤ rest.length at bounded
          omega
        · change remaining.witness.credit + (rest.length + 1) = before.credit + remaining.charges.sum
          have accounted := remaining.balance
          change remaining.witness.credit + rest.length = afterWitness.credit + remaining.charges.sum at accounted
          change afterWitness.credit + 1 = before.credit + charge at balance
          omega
      · obtain ⟨remaining⟩ := ih afterWitness
        refine ⟨⟨remaining.after, .cons ⟨advanced⟩ remaining.sourcePath, remaining.witness,
          charge :: remaining.charges, ?_, ?_, ?_, ?_⟩⟩
        · change remaining.charges.length + 1 = remaining.sourcePath.length + 1
          rw [remaining.chargedLength]
        · intro paid member
          rcases List.mem_cons.mp member with rfl | old
          · exact positiveCharge
          · exact remaining.positive paid old
        · change remaining.sourcePath.length + 1 ≤ rest.length + 1
          exact Nat.add_le_add_right remaining.length 1
        · change remaining.witness.credit + (rest.length + 1) =
            before.credit + (charge + remaining.charges.sum)
          have accounted := remaining.balance
          change remaining.witness.credit + rest.length = afterWitness.credit + remaining.charges.sum at accounted
          change afterWitness.credit + 1 = before.credit + charge at balance
          omega

/-- The initial credit comes from the same successful compiled body image,
with zero extra credit for the existing allocator guard and state token. -/
theorem initial_witness {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : SeedWorld Γ) (code : Code 0) (supplied : compile world.world process = some code) :
    ∃ witness : Witness world process (runtimeProcess code world.available),
      witness.credit = work process := by
  obtain ⟨image, initial, sourceEq, targetEq, balanced, credited⟩ :=
    RhoUnaryImage.initial_image_accounted guarded world.world code supplied
  let activities := image ++ [Activity.allocatorReady, .token world.available]
  have inventory : Inventory world activities := RhoUnaryInventory.initial_inventory world initial balanced
  have sourceImage : StructuralEq process (source activities) :=
    .trans sourceEq (.symm (RhoUnaryInitialRuntime.source_with_allocator image world.available))
  have actualImage := RhoUnaryInitialRuntime.actual_with_allocator world.world image code world.available targetEq
  have equation : Canonical.canonicalize (runtimeProcess code world.available).1 =
      Canonical.canonicalize (actual world.world activities) :=
    Canonical.canonicalize_eq_of_structuralCongruence actualImage
      (rhoProcWellSorted_hashSetFree ((ParameterizedRewriteSystem.process_iff _ _).mp
        (runtimeProcess code world.available).2).1)
      (rhoProcWellSorted_hashSetFree (parallel_typed (headers_typed world.world activities)))
  refine ⟨⟨Γ, .nil, world, activities, inventory, fun _ => rfl, le_rfl, sourceImage, equation⟩, ?_⟩
  simp only [Witness.credit, activities, total_append, total_cons, total_nil, credit, Nat.add_zero]
  exact credited

/-- Source compilation and every supplied actual target prefix now retain
both execution evidence and the exact primitive-work balance. -/
theorem compiled_prefix_accounted {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : SeedWorld Γ) (code : Code 0) (supplied : compile world.world process = some code)
    {final : TargetProcess} (path : ExecutionPath Target (runtimeProcess code world.available) final) :
    ∃ witness : Witness world process (runtimeProcess code world.available),
      witness.credit = work process ∧ Nonempty (PrefixResult witness path) := by
  obtain ⟨witness, credit⟩ := initial_witness guarded world code supplied
  exact ⟨witness, credit, retainPrefix witness path⟩

theorem terminal_source_length {Γ : Ctx sig} {process after : Proc Γ}
    (terminal : ∀ next, ¬ (operationalTheory Γ).Step process next)
    (path : ExecutionPath (operationalTheory Γ) process after) : path.length = 0 := by
  cases path with
  | refl => rfl
  | cons first rest => exact False.elim (terminal _ first.down)

/-- The bound applies at every represented phase, not only at the compiler's
initial runtime. It uses that phase's preserved occurrence credit. -/
theorem terminal_witness_prefix_bound {Γ : Ctx sig} {world : SeedWorld Γ}
    {process : Proc Γ} {current final : TargetProcess} (witness : Witness world process current)
    (terminal : ∀ after, ¬ (operationalTheory Γ).Step process after)
    (path : ExecutionPath Target current final) : path.length ≤ witness.credit := by
  obtain ⟨result⟩ := retainPrefix witness path
  have noSource : result.sourcePath.length = 0 := terminal_source_length terminal result.sourcePath
  have noCharges : result.charges = [] :=
    List.length_eq_zero_iff.mp (result.chargedLength.trans noSource)
  have balanced := result.balance
  rw [noCharges] at balanced
  simp only [List.sum_nil, Nat.add_zero] at balanced
  omega

/-- A source with no possible communication permits only finitely many
administrative target firings, irrespective of the chosen rho schedule. -/
theorem terminal_prefix_bound {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : SeedWorld Γ) (code : Code 0) (supplied : compile world.world process = some code)
    (terminal : ∀ after, ¬ (operationalTheory Γ).Step process after)
    {final : TargetProcess} (path : ExecutionPath Target (runtimeProcess code world.available) final) :
    path.length ≤ work process := by
  obtain ⟨witness, credited⟩ := initial_witness guarded world code supplied
  simpa only [credited] using terminal_witness_prefix_bound witness terminal path

/-- No schedule of actual authored target steps can manufacture an infinite
implementation-only run after the source is terminal. -/
private theorem transported_path_length {first second final : Target.Term}
    (same : first = second) (path : ExecutionPath Target first final) :
    (same ▸ path).length = path.length := by
  cases same
  rfl

theorem compiled_terminal_no_infinite_run {Γ : Ctx sig} {process : Proc Γ}
    (guarded : GuardedUnary process) (world : SeedWorld Γ) (code : Code 0)
    (supplied : compile world.world process = some code)
    (terminal : ∀ after, ¬ (operationalTheory Γ).Step process after) :
    ¬ ∃ states : Nat → Target.Term, states 0 = runtimeProcess code world.available ∧
      ∀ index, Target.Step (states index) (states (index + 1)) := by
  rintro ⟨states, starts, steps⟩
  have prefixes : ∀ count, ∃ path : ExecutionPath Target (states 0) (states count),
      path.length = count := by
    intro count
    induction count with
    | zero => exact ⟨.refl _, rfl⟩
    | succ count ih =>
        obtain ⟨path, counted⟩ := ih
        refine ⟨path.append (.cons ⟨steps count⟩ (.refl _)), ?_⟩
        exact (Route.length_append path (.cons ⟨steps count⟩ (.refl _))).trans
          (show path.length + 1 = count + 1 from congrArg (fun value => value + 1) counted)
  obtain ⟨path, counted⟩ := prefixes (work process + 1)
  have bound := terminal_prefix_bound guarded world code supplied terminal (starts ▸ path)
  have unchangedLength : (starts ▸ path).length = path.length := transported_path_length starts path
  rw [unchangedLength, counted] at bound
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
