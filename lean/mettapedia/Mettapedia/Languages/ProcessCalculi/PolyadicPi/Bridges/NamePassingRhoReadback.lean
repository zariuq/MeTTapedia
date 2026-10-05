import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoRuntime
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPublicObservation

/-!
# Actual rho prefixes of the whole lambda compiler read back to unary pi

All five source constructors enter the same actual rho runtime. Every
independently supplied authored target prefix yields a retained path of the
emitted unary protocol, including its literal final target state and the
current private-name world. No prescribed target schedule is required.

The intermediate path is a unary-pi path. Recovering a lambda path additionally
uses the private-session and source-environment reflection comparisons
composed in NamePassingSpine, including all related administrative phases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoReadback

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryWorld RhoUnaryReadback

/-- Active applications allocate a call/session pair; active definitions
allocate a reference/server pair. Suspended lambda and definition bodies
are initialized when they are released, rather than at program entry. -/
def initializationSites : {Γ : Ctx sig} → NamePassingLambda.Expr Γ → Nat
  | _, .var _ | _, .lam _ => 0
  | _, .app function _ => initializationSites function + 1
  | _, .defn _ body => initializationSites body + 1
  | _, .carrier _ _ body => initializationSites body

/-- The numeric entry cost is derived from the actual emitted private
protocol, independently of any chosen execution or eventual return. -/
theorem initial_work {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    RhoUnaryCredit.work (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) =
      8 * initializationSites term := by
  induction term generalizing Δ with
  | var =>
      rw [NamePassingLambda.compile, MonadicProtocol.lower_out1]
      simp only [out1, RhoUnaryCredit.work, initializationSites, Nat.mul_zero]
  | lam =>
      rw [NamePassingLambda.compile, MonadicProtocol.lower_inp2]
      simp only [MonadicProtocol.receivePair, inp1, RhoUnaryCredit.work, initializationSites, Nat.mul_zero]
  | app function argument ih =>
      rw [NamePassingLambda.compile, MonadicProtocol.lower_nu, MonadicProtocol.lower_par,
        MonadicProtocol.lower_out2]
      simp only [MonadicProtocol.sendPair, MonadicProtocol.sendFields, nu, par, out1, inp1,
        RhoUnaryCredit.work, ih, initializationSites, Nat.mul_add, Nat.mul_one]
      omega
  | defn value body _ bodyIH =>
      rw [NamePassingLambda.compile, MonadicProtocol.lower_nu, MonadicProtocol.lower_par,
        MonadicProtocol.lower_rep, MonadicProtocol.lower_inp1]
      simp only [nu, par, rep,
        RhoUnaryCredit.work, bodyIH, initializationSites, Nat.mul_add, Nat.mul_one]
      omega
  | carrier name value body _ bodyIH =>
      rw [NamePassingLambda.compile, MonadicProtocol.lower_par, MonadicProtocol.lower_inp1]
      simp only [par, inp1, RhoUnaryCredit.work, bodyIH, initializationSites, Nat.add_zero]

/-- Every whole-language compilation admits actual initialization at its
exact syntax-derived cost. The final supplied rho process retains the same
emitted source and has no pending administrative credit. -/
theorem initialized_runtime {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (world : SeedWorld Δ)
    (code : Code 0) (supplied : NamePassingRho.compile term environment result world.world = some code) :
    ∃ final : TargetProcess, ∃ path : ExecutionPath Target (runtimeProcess code world.available) final,
      ∃ witness : Witness world
        (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) final,
        witness.credit = 0 ∧ path.length = 8 * initializationSites term := by
  obtain ⟨before, credited⟩ := initial_witness
    (NamePassingRho.guarded_compiler_image term environment result) world code supplied
  obtain ⟨final, path, witness, zero, length⟩ := RhoUnaryAdministrativeProgress.drain before
  exact ⟨final, path, witness, zero, length.trans (credited.trans (initial_work term environment result))⟩

/-- The comparison consumes the real supplied compiler result and real
target path. Its unary endpoint remains related to that supplied rho endpoint. -/
theorem compiled_prefix {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (world : SeedWorld Δ)
    (code : Code 0) (supplied : NamePassingRho.compile term environment result world.world = some code)
    {final : TargetProcess}
    (path : ExecutionPath Target (runtimeProcess code world.available) final) :
    ∃ after, ∃ sourcePath : ExecutionPath (NativeTypes.operationalTheory Δ)
        (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) after,
      Related world after final ∧ sourcePath.length ≤ path.length :=
  RhoUnaryReadback.compiled_prefix
    (NamePassingRho.guarded_compiler_image term environment result) world code supplied path

/-- Every lambda expression has a fresh result channel and a successful
runtime entry for which the arbitrary-prefix theorem applies. -/
theorem fresh_compiled_prefix {Γ : Ctx sig} (term : NamePassingLambda.Expr Γ) :
    ∃ code : Code 0,
      NamePassingRho.compile term (fun _ name => Var.succ name) .zero
        (RhoUnaryWorld.initial (.nm :: Γ)).world = some code ∧
      ∀ {final : TargetProcess}
        (path : ExecutionPath Target
          (runtimeProcess code (Γ.length + 1)) final),
        ∃ after, ∃ sourcePath : ExecutionPath (NativeTypes.operationalTheory (.nm :: Γ))
            (MonadicProtocol.lower
              (NamePassingLambda.compile term (fun _ name => Var.succ name) .zero)) after,
          Related (RhoUnaryWorld.initial (.nm :: Γ)) after final ∧
            sourcePath.length ≤ path.length := by
  let world := RhoUnaryWorld.initial (.nm :: Γ)
  obtain ⟨code, supplied⟩ := NamePassingRho.compile_total term
    (fun _ name => Var.succ name) .zero world.world
  refine ⟨code, supplied, ?_⟩
  intro final path
  exact NamePassingRhoReadback.compiled_prefix term (fun _ name => Var.succ name) .zero
    world code supplied path

/-- The actual target prefix additionally retains the concrete source
activations and the exact balance of remaining initialization work. -/
theorem compiled_prefix_accounted {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (world : SeedWorld Δ)
    (code : Code 0) (supplied : NamePassingRho.compile term environment result world.world = some code)
    {final : TargetProcess}
    (path : ExecutionPath Target (runtimeProcess code world.available) final) :
    ∃ witness : Witness world
        (MonadicProtocol.lower (NamePassingLambda.compile term environment result))
        (runtimeProcess code world.available),
      witness.credit = RhoUnaryCredit.work
        (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) ∧
      Nonempty (PrefixResult witness path) :=
  RhoUnaryReadback.compiled_prefix_accounted
    (NamePassingRho.guarded_compiler_image term environment result) world code supplied path

/-- A visible output at the supplied endpoint is an actual public output
of the retained unary source path, rather than allocator or server traffic. -/
theorem compiled_public_output {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result channel : Var Δ .nm) (world : SeedWorld Δ)
    (code : Code 0) (supplied : NamePassingRho.compile term environment result world.world = some code)
    {final : TargetProcess}
    (path : ExecutionPath Target (runtimeProcess code world.available) final)
    (observed : Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveOutputObservation.HasOutput
      (world.world channel).term final.1) :
    ∃ after, ∃ sourcePath : ExecutionPath (NativeTypes.operationalTheory Δ)
        (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) after,
      Related world after final ∧ sourcePath.length ≤ path.length ∧
        PublicOutputObservation.HasOutput channel after := by
  obtain ⟨after, sourcePath, related, bound⟩ :=
    NamePassingRhoReadback.compiled_prefix term environment result world code supplied path
  exact ⟨after, sourcePath, related, bound,
    RhoUnaryPublicObservation.related_output_reflected world channel related observed⟩

/-- The concrete permitted observer also gives a native reachability
comparison for the emitted protocol of the whole lambda language. -/
theorem native_public_output_reflected {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result channel : Var Δ .nm) (world : SeedWorld Δ)
    (code : Code 0) (supplied : NamePassingRho.compile term environment result world.world = some code)
    (possible : (semanticDiamond Target.closure
      (RhoUnaryPublicObservation.targetPredicate world channel)).1
      (runtimeProcess code world.available)) :
    (semanticDiamond (NativeTypes.operationalTheory Δ).closure
      (PublicOutputObservation.closurePredicate channel)).1
        (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) :=
  RhoUnaryPublicObservation.native_may_output_reflected world channel
    (initial_related (NamePassingRho.guarded_compiler_image term environment result)
      world code supplied) possible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoReadback
