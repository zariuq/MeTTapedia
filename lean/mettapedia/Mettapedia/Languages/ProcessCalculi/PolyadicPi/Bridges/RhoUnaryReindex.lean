import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCredit

/-!
# Reindexing concrete unary implementation phases

Moving a source atom into a larger private-name context changes its source
indices and leaves its actual rho header unchanged when the name world is
pulled back along the same map. This holds for suspended private scopes,
all persistent-server phases and allocator phases, not only ordinary
communication. The laws allow the concrete reply receiver to bind a new
source name while every unrelated active occurrence keeps its endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReindex

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryClosing RhoUnaryNaturality
open RhoUnaryEnvironment RhoUnaryExecution RhoUnaryWorld RhoUnaryActive

def _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive.Activity.rename
    {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) : Activity Γ → Activity Δ
  | .output channel datum => .output (environment _ channel) (environment _ datum)
  | .input channel body guarded => .input (environment _ channel)
      (Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) body)
      (guarded.rename (liftRen environment [.nm]))
  | .privateScope body guarded => .privateScope
      (Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) body)
      (guarded.rename (liftRen environment [.nm]))
  | .install channel body guarded => .install (environment _ channel)
      (Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) body)
      (guarded.rename (liftRen environment [.nm]))
  | .ready channel body guarded self => .ready (environment _ channel)
      (Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) body)
      (guarded.rename (liftRen environment [.nm])) self
  | .rearm channel body guarded self => .rearm (environment _ channel)
      (Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) body)
      (guarded.rename (liftRen environment [.nm])) self
  | .sendCode channel body guarded self => .sendCode (environment _ channel)
      (Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) body)
      (guarded.rename (liftRen environment [.nm])) self
  | .request => .request
  | .reply seed => .reply seed
  | .allocatorReady => .allocatorReady
  | .allocatorRearm => .allocatorRearm
  | .allocatorSendCode => .allocatorSendCode
  | .seedInput => .seedInput
  | .token seed => .token seed

theorem _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive.Activity.source_rename
    {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    (activity.rename environment).source = rename environment activity.source := by
  cases activity <;> rfl

private theorem compiled_rename {Γ Δ : Ctx sig} {process : Proc Γ}
    (guarded : GuardedUnary process) {depth : Nat} (world : World Δ depth)
    (environment : Ren sig Γ Δ) :
    compiled (guarded.rename environment) world = compiled guarded (pullWorld world environment) := by
  apply compiled_eq
  rw [compile_rename guarded]
  exact compiled_spec guarded _

theorem ordinary_rename {Γ Δ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Δ 0) (environment : Ren sig Γ Δ) :
    ordinary (guarded.rename (liftRen environment [.nm])) world =
      ordinary guarded (pullWorld world environment) := by
  unfold ordinary
  rw [compiled_rename, pullWorld_lift]

theorem installBody_rename {Γ Δ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (world : World Δ 0)
    (environment : Ren sig Γ Δ) :
    installBody (environment _ channel) (guarded.rename (liftRen environment [.nm])) world =
      installBody channel guarded (pullWorld world environment) := by
  unfold installBody
  rw [compiled_rename, compiled_rename, pullWorld_serverHandler, pullWorld_storedHandler]
  rfl

theorem _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryActive.Activity.header_rename
    {Γ Δ : Ctx sig} (world : World Δ 0) (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    (activity.rename environment).header world = activity.header (pullWorld world environment) := by
  cases activity <;> simp only [Activity.rename, Activity.header, readyBody, stored]
  all_goals first | rfl | rw [ordinary_rename] | rw [installBody_rename]
  all_goals first | assumption | rfl

theorem headers_rename {Γ Δ : Ctx sig} (world : World Δ 0) (environment : Ren sig Γ Δ)
    (activities : List (Activity Γ)) :
    headers world (activities.map (Activity.rename environment)) =
      headers (pullWorld world environment) activities := by
  simp only [headers, List.map_map]
  apply List.map_congr_left
  intro activity _
  exact activity.header_rename world environment

theorem source_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    source (activities.map (Activity.rename environment)) = rename environment (source activities) := by
  rw [source, source, ScopedActiveFrontier.parallel_rename, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro activity _
  exact activity.source_rename environment

/-- Installing one actual returned seed extends the source context; all
unrelated active headers retain their literal rho representation. -/
theorem headers_extendAt {Γ : Ctx sig} (world : SeedWorld Γ) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    (activities : List (Activity Γ)) :
    headers (world.extendAt seed returned fresh).world
        (activities.map (Activity.rename (fun _ name => Var.succ name))) =
      headers world.world activities := by
  rw [headers_rename]
  rfl


/-- Reindexing the source-name world changes no outstanding primitive work. -/
theorem _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCredit.credit_rename
    {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    RhoUnaryCredit.credit (activity.rename environment) = RhoUnaryCredit.credit activity := by
  cases activity with
  | privateScope body guarded =>
      simp only [Activity.rename, RhoUnaryCredit.credit]
      rw [RhoUnaryCredit.work_rename guarded]
  | output channel datum => rfl
  | input channel body guarded => rfl
  | install channel body guarded => rfl
  | ready channel body guarded self => rfl
  | rearm channel body guarded self => rfl
  | sendCode channel body guarded self => rfl
  | request => rfl
  | reply seed => rfl
  | allocatorReady => rfl
  | allocatorRearm => rfl
  | allocatorSendCode => rfl
  | seedInput => rfl
  | token seed => rfl

theorem _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCredit.total_rename
    {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    RhoUnaryCredit.total (activities.map (Activity.rename environment)) = RhoUnaryCredit.total activities := by
  simp only [RhoUnaryCredit.total, List.map_map, Function.comp_def, RhoUnaryCredit.credit_rename]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReindex
