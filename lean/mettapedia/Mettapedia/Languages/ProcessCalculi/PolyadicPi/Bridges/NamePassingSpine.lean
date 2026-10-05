import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryNormalization
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOperationalNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNormalizationAgreement
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredNativeTypes

/-!
# The name-passing lambda, scoped pi and core-rho execution spine

The actual compiler factors through the scoped polyadic interpretation and
the private-session unary protocol. The independently proved comparisons
compose over all related administrative states. Every supplied core-rho
prefix retains its original endpoint and a genuine lambda prefix; allowed
returned-function observations and strong normalization agree both ways.

The observers are public result-channel receivers. Quoted implementation
structure and arbitrary target contexts are additional observations. The
accounts count actual primitive communications, including allocation and
server rearming, rather than physical time or funded purse expenditure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative NamePassingUnaryForward
open RhoUnaryCode RhoUnaryWorld

abbrev World (Γ : Ctx sig) := SeedWorld (.nm :: Γ)

/-- Both components have independent actual-step reflection and forward
execution laws. The middle state is retained in their relational composition. -/
def correspondence {Γ : Ctx sig} (world : World Γ) :
    OperationalCorrespondence (sourceTheory Γ) RhoUnaryReadback.Target :=
  (NamePassingUnaryOperational.correspondence Γ).comp
    (RhoUnaryOperationalNative.correspondence world)

theorem initial_related {Γ : Ctx sig} (source : Expr Γ) (world : World Γ) (code : Code 0)
    (supplied : NamePassingRho.compile source (references Γ) .zero world.world = some code) :
    (correspondence world).related source (RhoUnaryReadback.runtimeProcess code world.available) :=
  ⟨unary source, NamePassingUnaryOperational.compiled_related source,
    RhoUnaryReadback.initial_related (NamePassingRho.guarded_compiler_image source (references Γ) .zero)
      world code supplied⟩

/-- Every source expression has a real successful compilation for which the
complete correspondence applies, so the compiler image is not an empty class. -/
theorem compilation_exists {Γ : Ctx sig} (source : Expr Γ) :
    ∃ code : Code 0,
      NamePassingRho.compile source (references Γ) .zero (RhoUnaryWorld.initial (.nm :: Γ)).world = some code ∧
      (correspondence (RhoUnaryWorld.initial (.nm :: Γ))).related source
        (RhoUnaryReadback.runtimeProcess code (RhoUnaryWorld.initial (.nm :: Γ)).available) := by
  obtain ⟨code, supplied⟩ := NamePassingRho.compile_total source (references Γ) .zero
    (RhoUnaryWorld.initial (.nm :: Γ)).world
  exact ⟨code, supplied, initial_related source (RhoUnaryWorld.initial (.nm :: Γ)) code supplied⟩

/-- A supplied actual target prefix, including arbitrary scheduling and
equation representatives, has a lambda prefix at its exact related endpoint. -/
theorem prefix_readback {Γ : Ctx sig} (world : World Γ)
    {source : Expr Γ} {current final : RhoUnaryReadback.TargetProcess}
    (related : (correspondence world).related source current)
    (actual : ExecutionPath RhoUnaryReadback.Target current final) :
    ∃ after, ∃ path : ExecutionPath (sourceTheory Γ) source after,
      (correspondence world).related after final ∧ path.length ≤ actual.length :=
  (correspondence world).reflectPath related actual

structure PrefixResult {Γ : Ctx sig} (source : Expr Γ) (world : World Γ) (code : Code 0)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) where
  after : Expr Γ
  middle : Proc (.nm :: Γ)
  sourcePath : ExecutionPath (sourceTheory Γ) source after
  unaryPath : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ)) (unary source) middle
  protocol : MonadicProtocol.RuntimeWitness.Witness (polyadic after) middle
  rho : RhoUnaryReadback.Witness world middle final
  sourceLength : sourcePath.length ≤ unaryPath.length
  unaryLength : unaryPath.length ≤ actual.length
  protocolBalance : protocol.debt + unaryPath.length ≤ 4 * sourcePath.length
  charges : List Nat
  chargedLength : charges.length = unaryPath.length
  positive : ∀ charge ∈ charges, 0 < charge
  rhoBalance : rho.credit + actual.length = 8 * NamePassingRhoReadback.initializationSites source + charges.sum

/-- Actual source and unary paths, intermediate occurrence witnesses and
rho activation charges stay together. The rho initialization amount is
derived from the emitted syntax, independently of the target execution. -/
theorem compiled_prefix_accounted {Γ : Ctx sig} (source : Expr Γ) (world : World Γ) (code : Code 0)
    (supplied : NamePassingRho.compile source (references Γ) .zero world.world = some code)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    Nonempty (PrefixResult source world code actual) := by
  obtain ⟨rhoBefore, credit⟩ := RhoUnaryReadback.initial_witness
    (NamePassingRho.guarded_compiler_image source (references Γ) .zero) world code supplied
  obtain ⟨rhoReceipt⟩ := RhoUnaryReadback.retainPrefix rhoBefore actual
  obtain ⟨after, sourcePath, protocol, sourceLength, protocolBalance⟩ :=
    NamePassingUnaryOperational.compiled_prefix source rhoReceipt.sourcePath
  refine ⟨⟨after, rhoReceipt.after, sourcePath, rhoReceipt.sourcePath, protocol, rhoReceipt.witness,
    sourceLength, rhoReceipt.length, protocolBalance, rhoReceipt.charges, rhoReceipt.chargedLength,
    rhoReceipt.positive, ?_⟩⟩
  have initialCredit := credit.trans (NamePassingRhoReadback.initial_work source (references Γ) .zero)
  exact rhoReceipt.balance.trans (congrArg (fun amount => amount + rhoReceipt.charges.sum) initialCredit)

/-- An actual public result receiver cannot appear before the related source
has returned a function. This concerns the supplied current target state. -/
theorem current_return_reflected {Γ : Ctx sig} (world : World Γ)
    {source : Expr Γ} {current : RhoUnaryReadback.TargetProcess}
    (related : (correspondence world).related source current)
    (observed : (RhoUnaryInputObservation.targetPredicate world .zero).1 current) :
    (NamePassingValueNative.sourcePredicate Γ).1 source := by
  obtain ⟨middle, protocol, rho⟩ := related
  exact NamePassingUnaryNative.current_return_reflected protocol
    (RhoUnaryInputObservation.related_input_reflected world .zero rho observed)

/-- A returned function becomes visible after actual finite administration,
including any pending tuple receipts and core-rho allocation work. -/
theorem current_return_realized {Γ : Ctx sig} (world : World Γ)
    {source : Expr Γ} {current : RhoUnaryReadback.TargetProcess}
    (related : (correspondence world).related source current)
    (returned : (NamePassingValueNative.sourcePredicate Γ).1 source) :
    (semanticDiamond RhoUnaryReadback.Target.closure
      (RhoUnaryInputObservation.targetPredicate world .zero)).1 current := by
  obtain ⟨middle, protocol, rho⟩ := related
  exact (RhoUnaryOperationalNative.native_may_input_iff world .zero rho).mp
    (NamePassingUnaryNative.current_return_realized protocol returned)

/-- Every supplied returning prefix retains a genuine returned source state
alongside its exact target endpoint, both execution paths and work balances. -/
theorem compiled_return_accounted {Γ : Ctx sig} (source : Expr Γ) (world : World Γ)
    (code : Code 0)
    (supplied : NamePassingRho.compile source (references Γ) .zero world.world = some code)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final)
    (observed : (RhoUnaryInputObservation.targetPredicate world .zero).1 final) :
    ∃ receipt : PrefixResult source world code actual,
      (NamePassingValueNative.sourcePredicate Γ).1 receipt.after := by
  obtain ⟨receipt⟩ := compiled_prefix_accounted source world code supplied actual
  exact ⟨receipt, current_return_reflected world
    ⟨receipt.middle, ⟨receipt.protocol⟩, ⟨receipt.rho⟩⟩ observed⟩

/-- The generated reachability type for returned functions is preserved
and reflected by the composed compiler under the public result observer. -/
theorem native_may_return_iff {Γ : Ctx sig} (world : World Γ)
    {source : Expr Γ} {current : RhoUnaryReadback.TargetProcess}
    (related : (correspondence world).related source current) :
    (semanticDiamond (sourceTheory Γ).closure (NamePassingValueNative.sourcePredicate Γ)).1 source ↔
      (semanticDiamond RhoUnaryReadback.Target.closure
        (RhoUnaryInputObservation.targetPredicate world .zero)).1 current := by
  obtain ⟨middle, protocol, rho⟩ := related
  exact (NamePassingUnaryNative.native_may_return_iff protocol).trans
    (RhoUnaryOperationalNative.native_may_input_iff world .zero rho)

/-- Every actual schedule terminates precisely when the source strongly
normalizes. Both stages exclude an infinite run of administration alone. -/
theorem accessibility_iff {Γ : Ctx sig} (world : World Γ)
    {source : Expr Γ} {current : RhoUnaryReadback.TargetProcess}
    (related : (correspondence world).related source current) :
    Acc (fun after before => (sourceTheory Γ).Step before after) source ↔
      Acc (fun after state => RhoUnaryReadback.Target.Step state after) current := by
  obtain ⟨middle, protocol, ⟨rho⟩⟩ := related
  exact (NamePassingUnaryNormalization.accessibility_iff protocol).trans
    (RhoUnaryNormalizationAgreement.accessibility_iff rho)

theorem infinite_execution_iff {Γ : Ctx sig} (world : World Γ)
    {source : Expr Γ} {current : RhoUnaryReadback.TargetProcess}
    (related : (correspondence world).related source current) :
    (∃ execution : Nat → Expr Γ, execution 0 = source ∧
      ∀ index, (sourceTheory Γ).Step (execution index) (execution (index + 1))) ↔
    (∃ runtime : Nat → RhoUnaryReadback.TargetProcess, runtime 0 = current ∧
      ∀ index, RhoUnaryReadback.Target.Step (runtime index) (runtime (index + 1))) := by
  constructor
  · intro execution
    have divergent : ¬ Acc (fun after before => (sourceTheory Γ).Step before after) source :=
      not_acc_iff_exists_descending_chain.mpr execution
    exact not_acc_iff_exists_descending_chain.mp
      (fun normalizing => divergent ((accessibility_iff world related).mpr normalizing))
  · intro execution
    have divergent : ¬ Acc (fun after state => RhoUnaryReadback.Target.Step state after) current :=
      not_acc_iff_exists_descending_chain.mpr execution
    exact not_acc_iff_exists_descending_chain.mp
      (fun normalizing => divergent ((accessibility_iff world related).mp normalizing))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine
