import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCredit

/-!
# Every guarded unary compiler result has a concrete active image

Parallel composition is flattened using the existing rho equations. Private
scopes and persistent listeners yield both their real allocator request and
their suspended reply continuation. Input bodies remain guarded. The source
readout equals the original source modulo its own structural equations;
the actual header bag equals the supplied compiler result modulo rho's.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryImage

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryActive RhoUnaryCredit
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-- No live server or allocator phase is invented at compiler entry. -/
def Initial {Γ : Ctx sig} : Activity Γ → Prop
  | .output _ _ | .input _ _ _ | .privateScope _ _ | .install _ _ _ | .request => True
  | _ => False

def pendingWeight {Γ : Ctx sig} : Activity Γ → Nat
  | .privateScope _ _ | .install _ _ _ => 1
  | _ => 0

def requestWeight {Γ : Ctx sig} : Activity Γ → Nat
  | .request => 1
  | _ => 0

def clientCount {Γ : Ctx sig} (activities : List (Activity Γ)) : Nat :=
  (activities.map pendingWeight).sum

def requestCount {Γ : Ctx sig} (activities : List (Activity Γ)) : Nat :=
  (activities.map requestWeight).sum

theorem actual_append {Γ : Ctx sig} (world : World Γ 0)
    (first second : List (Activity Γ)) :
    StructuralCongruence (RhoScopedServers.parallel [actual world first, actual world second])
      (actual world (first ++ second)) := by
  simpa [actual, headers, HeaderInversion.parallel, List.map_append] using
    Context.par_sc_flatten_bags ((headers world first).map Header.pattern)
      ((headers world second).map Header.pattern)

theorem source_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    StructuralEq (par (source first) (source second)) (source (first ++ second)) := by
  simpa [source, List.map_append] using
    ScopedActiveFrontier.parallel_append (first.map Activity.source) (second.map Activity.source)

private theorem initial_pair_source {Γ : Ctx sig} (first : Activity Γ)
    (noSource : Activity Γ) (empty : noSource.source = nil) :
    StructuralEq (source [first, noSource]) first.source := by
  change StructuralEq (par first.source (par noSource.source nil)) first.source
  rw [empty]
  exact .trans (.par (.refl _) (.parUnit _)) (.parUnit _)

/-- A supplied successful compiler output, rather than an independently
chosen encoding, is the actual initial header image of the whole fragment. -/
theorem initial_image_accounted {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process) :
    ∀ (world : World Γ 0) (code : Code 0), compile world process = some code →
    ∃ activities : List (Activity Γ),
      (∀ activity ∈ activities, Initial activity) ∧
      StructuralEq process (source activities) ∧
      StructuralCongruence code.term (actual world activities) ∧
      clientCount activities = requestCount activities ∧ total activities = work process := by
  induction guarded with
  | nil =>
      intro world code codeEq
      have same : code = Code.zero 0 := by simpa [compile, nil] using codeEq.symm
      subst code
      refine ⟨[], by simp, .refl _, .symm _ _ StructuralCongruence.par_empty, rfl, ?_⟩
      simp [total, nil, work]
  | par firstG secondG firstIH secondIH =>
      intro world code codeEq
      obtain ⟨first, firstEq⟩ := compile_guarded firstG world
      obtain ⟨second, secondEq⟩ := compile_guarded secondG world
      have same : code = Code.par first second := by
        simpa [compile, par, firstEq, secondEq] using codeEq.symm
      subst code
      obtain ⟨firstActivities, firstInitial, firstSource, firstTarget, firstBalanced, firstCredit⟩ := firstIH world first firstEq
      obtain ⟨secondActivities, secondInitial, secondSource, secondTarget, secondBalanced, secondCredit⟩ := secondIH world second secondEq
      refine ⟨firstActivities ++ secondActivities, ?_, ?_, ?_, ?_, ?_⟩
      · intro activity membership
        rcases List.mem_append.mp membership with member | member
        · exact firstInitial activity member
        · exact secondInitial activity member
      · exact .trans (.par firstSource secondSource) (source_append firstActivities secondActivities)
      · refine .trans _ _ _ ?_ (actual_append world firstActivities secondActivities)
        apply StructuralCongruence.par_cong [first.term, second.term]
          [actual world firstActivities, actual world secondActivities] rfl
        intro index leftBound rightBound
        match index with
        | 0 => exact firstTarget
        | 1 => exact secondTarget
        | index + 2 => simp at leftBound
      · simp only [clientCount, requestCount, List.map_append, List.sum_append]
        change clientCount firstActivities + clientCount secondActivities =
          requestCount firstActivities + requestCount secondActivities
        rw [firstBalanced, secondBalanced]
      · simp only [total_append, par, work, firstCredit, secondCredit]
  | inp1 channel bodyG bodyIH =>
      intro world code codeEq
      cases channel with
      | op op args => cases op
      | var channel =>
          have same : code = Code.listen (world channel) (ordinary bodyG world) := by
            simpa [compile, inp1, evalName, ordinary, compiled_spec bodyG (liftWorld world)] using codeEq.symm
          subst code
          refine ⟨[.input channel _ bodyG], by simp [Initial], ?_, ?_, rfl, ?_⟩
          · exact .symm (.parUnit _)
          · exact .symm _ _ (StructuralCongruence.par_singleton _)
          · simp [total, credit, inp1, work]
  | out1 channel datum =>
      intro world code codeEq
      cases channel with
      | op op args => cases op
      | var channel =>
          cases datum with
          | op op args => cases op
          | var datum =>
              have same : code = Code.sendName (world channel) (world datum) := by
                simpa [compile, out1, evalName] using codeEq.symm
              subst code
              refine ⟨[.output channel datum], by simp [Initial], ?_, ?_, rfl, ?_⟩
              · exact .symm (.parUnit _)
              · exact .symm _ _ (StructuralCongruence.par_singleton _)
              · simp [total, credit, out1, work]
  | nu bodyG bodyIH =>
      intro world code codeEq
      have same : code = Code.reserve (ordinary bodyG world) := by
        simpa [compile, nu, ordinary, compiled_spec bodyG (liftWorld world)] using codeEq.symm
      subst code
      refine ⟨[.privateScope _ bodyG, .request], by simp [Initial], ?_, ?_, rfl, ?_⟩
      · exact .symm (initial_pair_source (.privateScope _ bodyG) .request rfl)
      · apply StructuralCongruence.par_perm
        exact List.Perm.swap _ _ []
      · simp [total, credit, nu, work, Nat.add_comm]
  | server channel bodyG bodyIH =>
      intro world code codeEq
      cases channel with
      | op op args => cases op
      | var channel =>
          have same : code = Code.reserve (installBody channel bodyG world) := by
            simpa [compile, rep, inp1, installBody, evalName,
              compiled_spec bodyG (serverHandlerWorld world),
              compiled_spec bodyG (storedHandlerWorld world)] using codeEq.symm
          subst code
          refine ⟨[.install channel _ bodyG, .request], by simp [Initial], ?_, ?_, rfl, ?_⟩
          · exact .symm (initial_pair_source (.install channel _ bodyG) .request rfl)
          · apply StructuralCongruence.par_perm
            exact List.Perm.swap _ _ []
          · simp [total, credit, rep, work]

/-- Formation and pending balance are projections of the same accounted
image construction, retaining its real compiler output and source readout. -/
theorem initial_image_balanced {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : World Γ 0) (code : Code 0) (supplied : compile world process = some code) :
    ∃ activities : List (Activity Γ),
      (∀ activity ∈ activities, Initial activity) ∧
      StructuralEq process (source activities) ∧
      StructuralCongruence code.term (actual world activities) ∧
      clientCount activities = requestCount activities := by
  obtain ⟨activities, initial, sourceEq, targetEq, balanced, _⟩ :=
    initial_image_accounted guarded world code supplied
  exact ⟨activities, initial, sourceEq, targetEq, balanced⟩

/-- The formation-only interface is the projection of the same balanced
initial image, so clients cannot receive a competing representation. -/
theorem initial_image {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process)
    (world : World Γ 0) (code : Code 0) (supplied : compile world process = some code) :
    ∃ activities : List (Activity Γ),
      (∀ activity ∈ activities, Initial activity) ∧
      StructuralEq process (source activities) ∧
      StructuralCongruence code.term (actual world activities) := by
  obtain ⟨activities, initial, sourceEq, targetEq, _⟩ :=
    initial_image_balanced guarded world code supplied
  exact ⟨activities, initial, sourceEq, targetEq⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryImage
