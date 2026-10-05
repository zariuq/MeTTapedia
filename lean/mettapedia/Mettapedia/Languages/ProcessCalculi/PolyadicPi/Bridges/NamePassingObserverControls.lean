import Mettapedia.Languages.LambdaCalculus.NamePassingPure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls

/-!
# Callers distinguish returned functions; quotes remain a separate observer

Both functions below return immediately. Applying them to an unprovided free
name distinguishes them: the identity blocks, while the constant function
returns another function. The same admitted client distinguishes their actual
rho executions. Structural source equations remain valid in every admitted
client. The quoted implementation test is retained alongside this boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open NamePassingLambda NamePassingContexts NamePassingEnvironmentEquationsNative
open NamePassingObserverAdequacy

abbrev names : Ctx sig := [.nm]

def identity : Expr names := .lam (.var .zero)
def constant : Expr names := .lam (.lam (.var .zero))
def free : Expr names := .var .zero
def caller : SourceContext names names := .app .hole .zero

private theorem variable_path {Γ : Ctx sig} (name : Var Γ .nm) {final : Expr Γ}
    (path : (sourceTheory Γ).MultiStep (.var name) final) : final = .var name := by
  obtain ⟨execution⟩ := (executionPath_nonempty_iff_multiStep (sourceTheory Γ) _ _).mpr path
  cases execution with
  | refl => rfl
  | cons first _ =>
      obtain ⟨action, firing⟩ := first.down
      exact (NamePassing.variable_no_modulo_step name firing).elim

theorem free_does_not_return : ¬ MayReturn free := by
  intro returned
  obtain ⟨final, path, observed⟩ := (closure_nativeDiamond_iff (sourceTheory names) _ free).mp returned
  have same := variable_path .zero path
  subst final
  cases observed

theorem identity_returns : MayReturn identity :=
  (closure_nativeDiamond_iff (sourceTheory names) _ identity).mpr ⟨identity, .refl _, rfl⟩

theorem constant_returns : MayReturn constant :=
  (closure_nativeDiamond_iff (sourceTheory names) _ constant).mpr ⟨constant, .refl _, rfl⟩

/-- This call has only its beta step and then blocks at the supplied name. -/
theorem identity_call_does_not_return : ¬ MayReturn (caller.plug identity) := by
  intro returned
  obtain ⟨final, path, observed⟩ :=
    (closure_nativeDiamond_iff (sourceTheory names) _ (caller.plug identity)).mp returned
  obtain ⟨execution⟩ := (executionPath_nonempty_iff_multiStep (sourceTheory names) _ _).mpr path
  cases execution with
  | refl => cases observed
  | cons first rest =>
      obtain ⟨action, firing⟩ := first.down
      obtain ⟨_, same⟩ := NamePassing.identity_modulo_step (.zero : Var names .nm) firing
      rw [same] at rest
      have finalEq := variable_path .zero (executionPathToMultiStep rest)
      subst final
      cases observed

theorem constant_call_returns : MayReturn (caller.plug constant) := by
  apply (closure_nativeDiamond_iff (sourceTheory names) _ _).mpr
  exact ⟨identity, .step ⟨.beta, (NamePassing.Environment.Step.beta
    (.lam (.var .zero)) (.zero : Var names .nm)).toModulo⟩ (.refl _), rfl⟩

theorem admitted_call_distinguishes_actual_execution :
    Admitted (translate caller) ∧
      ¬ ProtocolMayReturn ((translate caller).plug (program identity)) ∧
      ProtocolMayReturn ((translate caller).plug (program constant)) :=
  ⟨translated_admitted caller, fun returned => identity_call_does_not_return
    ((context_mayReturn_iff caller identity).mpr returned),
    (context_mayReturn_iff caller constant).mp constant_call_returns⟩

theorem plain_return_is_insufficient :
    (MayReturn identity ↔ MayReturn constant) ∧ ¬ SourceEquivalent identity constant := by
  refine ⟨iff_of_true identity_returns constant_returns, ?_⟩
  intro equivalent
  exact identity_call_does_not_return ((equivalent names caller).mpr constant_call_returns)

theorem compiled_functions_are_contextually_distinct :
    ¬ ProtocolEquivalent (program identity) (program constant) :=
  fun equivalent => plain_return_is_insufficient.2 ((contextual_adequacy identity constant).mpr equivalent)

/-- Moving application through a fresh nonrecursive definition changes no
admitted observation, including later calls and stored-value clients. -/
theorem definition_scope_equation_survives_all_clients {Γ : Ctx sig}
    (value : Expr Γ) (body : Expr (.nm :: Γ)) (argument : Var Γ .nm) :
    ProtocolEquivalent (program (.app (.defn value body) argument))
      (program (.defn value (.app body (.succ argument)))) :=
  (contextual_adequacy _ _).mp
    (structural_equivalent (.appDefinition value body argument))

/-- The admitted caller result coexists with the operational quotation
counterexample; extending the observer language requires another contract. -/
theorem quotation_boundary_is_operational :
    (∃ after, (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem.theory
      Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping.rhoAtomicNameContext).Step
      (RhoQuotedCompilerObserverControls.testProcess (RhoUnaryCode.Code.reserve (RhoUnaryCode.Code.zero 1)))
      after) ∧
    (∀ after, ¬ (Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParameterizedRewriteSystem.theory
      Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping.rhoAtomicNameContext).Step
      (RhoQuotedCompilerObserverControls.testProcess (RhoUnaryCode.Code.zero 0)) after) :=
  ⟨RhoQuotedCompilerObserverControls.allocation_quote_answers,
    RhoQuotedCompilerObserverControls.inaction_quote_cannot_answer⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverControls
