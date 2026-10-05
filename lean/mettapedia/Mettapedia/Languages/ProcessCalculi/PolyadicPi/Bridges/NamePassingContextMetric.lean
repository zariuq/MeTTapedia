import Mettapedia.GSLT.Logic.BudgetedObservations
import Mettapedia.Languages.LambdaCalculus.NamePassingContextBudget
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy

/-!
# Contextual distance preserved by certified protocol clients

The test budget is an authored source-context price. A target client retains
its elaboration origin, so two clients have the same declared price under
transport. The target predicate still executes the independently assembled
pi program through the actual unary/rho pipeline. Every admitted client has
such a certificate. This gives a nontrivial contextual ultrapseudometric,
not a claim that primitive rho communication distance equals lambda distance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContextMetric

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Logic
open Mettapedia.Languages.LambdaCalculus
open NamePassingLambda NamePassingContexts NamePassingObserverAdequacy

abbrev SourceTest (Γ : Ctx sig) := (Δ : Ctx sig) × SourceContext Γ Δ

structure CertifiedClient (Γ : Ctx sig) where
  output : Ctx sig
  client : ProtocolContexts.Context Γ output
  origin : SourceContext Γ output
  elaborates : translate origin = client

def certify {Γ : Ctx sig} (test : SourceTest Γ) : CertifiedClient Γ :=
  ⟨test.1, translate test.2, test.2, rfl⟩

theorem certify_covers (Γ : Ctx sig) : Function.Surjective (certify (Γ := Γ)) := by
  rintro ⟨output, client, origin, elaborates⟩
  subst client
  exact ⟨⟨output, origin⟩, rfl⟩

theorem certified_admitted {Γ : Ctx sig} (client : CertifiedClient Γ) : Admitted client.client :=
  ⟨client.origin, client.elaborates⟩

theorem admitted_has_certificate {Γ Δ : Ctx sig} (client : ProtocolContexts.Context Γ Δ)
    (admitted : Admitted client) :
    ∃ certificate : CertifiedClient Γ, ∃ equal : certificate.output = Δ,
      equal ▸ certificate.client = client := by
  obtain ⟨origin, elaborates⟩ := admitted
  exact ⟨⟨Δ, client, origin, elaborates⟩, rfl, rfl⟩

noncomputable def testWeight {Γ : Ctx sig} (test : SourceTest Γ) : ℝ :=
  (1 / 2 : ℝ) ^ test.2.budget

theorem testWeight_positive {Γ : Ctx sig} (test : SourceTest Γ) : 0 < testWeight test :=
  pow_pos (by norm_num) _

theorem testWeight_bounded {Γ : Ctx sig} (test : SourceTest Γ) : testWeight test ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

noncomputable def sourceTests (Γ : Ctx sig) : BudgetedObservations (Expr Γ) where
  Test := SourceTest Γ
  holds test source := MayReturn (test.2.plug source)
  weight := testWeight
  positive := testWeight_positive
  bounded := testWeight_bounded

noncomputable def targetTests (Γ : Ctx sig) : BudgetedObservations (ProtocolContexts.Program Γ) where
  Test := CertifiedClient Γ
  holds test component := ProtocolMayReturn (test.client.plug component)
  weight test := testWeight ⟨test.output, test.origin⟩
  positive test := testWeight_positive ⟨test.output, test.origin⟩
  bounded test := testWeight_bounded ⟨test.output, test.origin⟩

theorem contextual_distance_eq {Γ : Ctx sig} (left right : Expr Γ) :
    (targetTests Γ).distance (program left) (program right) = (sourceTests Γ).distance left right :=
  (sourceTests Γ).distance_transport (targetTests Γ) program certify (certify_covers Γ)
    (fun test source => (context_mayReturn_iff test.2 source).symm) (fun _ => rfl) left right

theorem source_zero_iff {Γ : Ctx sig} (left right : Expr Γ) :
    (sourceTests Γ).distance left right = 0 ↔ SourceEquivalent left right := by
  rw [(sourceTests Γ).distance_eq_zero_iff]
  constructor
  · intro same Δ context
    exact same ⟨Δ, context⟩
  · intro same test
    exact same test.1 test.2

theorem target_zero_iff {Γ : Ctx sig} (left right : ProtocolContexts.Program Γ) :
    (targetTests Γ).distance left right = 0 ↔ ProtocolEquivalent left right := by
  rw [(targetTests Γ).distance_eq_zero_iff]
  constructor
  · intro same Δ client admitted
    obtain ⟨origin, elaborates⟩ := admitted
    exact same ⟨Δ, client, origin, elaborates⟩
  · intro same test
    exact same test.output test.client (certified_admitted test)

private theorem score_compose {Γ Δ : Ctx sig} (context : SourceContext Γ Δ)
    (test : SourceTest Δ) (left right : Expr Γ) :
    (sourceTests Γ).score ⟨test.1, test.2.compose context⟩ left right =
      (sourceTests Δ).score test (context.plug left) (context.plug right) *
        (1 / 2 : ℝ) ^ context.budget := by
  classical
  simp only [BudgetedObservations.score, sourceTests, testWeight,
    NamePassing.Context.plug_compose, NamePassing.Context.budget_compose, pow_add]
  split_ifs <;> simp_all

/-- Fixing a client moves its cost from the test into the compared program.
Its price gives the precise budget-scaled bound; unpriced context
nonexpansiveness is not inferred. -/
theorem context_budget_bound {Γ Δ : Ctx sig} (context : SourceContext Γ Δ) (left right : Expr Γ) :
    (sourceTests Δ).distance (context.plug left) (context.plug right) *
      (1 / 2 : ℝ) ^ context.budget ≤ (sourceTests Γ).distance left right := by
  have positive : 0 < (1 / 2 : ℝ) ^ context.budget := pow_pos (by norm_num) _
  apply (le_div_iff₀ positive).mp
  apply ((sourceTests Δ).distance_le_iff _ _ _).mpr
  refine ⟨div_nonneg ((sourceTests Γ).distance_nonneg left right) positive.le, ?_⟩
  intro test
  change SourceTest Δ at test
  apply (le_div_iff₀ positive).mpr
  rw [← score_compose context test left right]
  exact (sourceTests Γ).score_le_distance ⟨test.1, test.2.compose context⟩ left right

theorem compiled_context_budget_bound {Γ Δ : Ctx sig} (context : SourceContext Γ Δ)
    (left right : Expr Γ) :
    (targetTests Δ).distance ((translate context).plug (program left))
      ((translate context).plug (program right)) * (1 / 2 : ℝ) ^ context.budget ≤
        (targetTests Γ).distance (program left) (program right) := by
  rw [plug_agreement, plug_agreement, contextual_distance_eq, contextual_distance_eq]
  exact context_budget_bound context left right

private theorem zero_budget_observation {Γ Δ : Ctx sig} (context : SourceContext Γ Δ)
    (zero : context.budget = 0) {left right : Expr Γ} (same : MayReturn left ↔ MayReturn right) :
    MayReturn (context.plug left) ↔ MayReturn (context.plug right) := by
  cases context <;> simp only [NamePassing.Context.budget] at zero
  · exact same
  all_goals omega

/-- When the empty client cannot distinguish the programs, any distinguishing
client must pay for at least one authored constructor. -/
theorem distance_le_half_of_mayReturn_agreement {Γ : Ctx sig} {left right : Expr Γ}
    (same : MayReturn left ↔ MayReturn right) :
    (sourceTests Γ).distance left right ≤ (1 / 2 : ℝ) := by
  classical
  apply ((sourceTests Γ).distance_le_iff _ _ _).mpr
  refine ⟨by norm_num, ?_⟩
  intro test
  change SourceTest Γ at test
  by_cases zero : test.2.budget = 0
  · have equalReading := zero_budget_observation test.2 zero same
    change (if MayReturn (test.2.plug left) ↔ MayReturn (test.2.plug right) then (0 : ℝ)
      else testWeight test) ≤ _
    rw [if_pos equalReading]
    norm_num
  · have positive : 1 ≤ test.2.budget := Nat.one_le_iff_ne_zero.mpr zero
    have decreasing := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) positive
    exact ((sourceTests Γ).score_le_weight test left right).trans
      (by simpa [sourceTests, testWeight] using decreasing)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContextMetric
