import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersCached
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersNested
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersQuoted
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersMiller

/-!
# β and activation along runs, with the actual incremental solver

β's right-hand side `$B[$A]` is not a Miller pattern, so the store leaves the pattern fragment
after one β firing. The equations are determinate, though, and their left-hand sides are Miller
patterns, in every context.
- `atContext_determinate`: plugging keeps an equation determinate.
- `lambda_with_solvers`: runs of the four-rule λ step are exactly the readings of runs of the
  binder-bearing core in λ contexts whose every firing has a completed incremental solver result,
  hence a principal answer.
- `quoted_with_solvers`: the same for the quoted-λ account, with β and activation.
- `two_answers_with_solvers`: the two-branch control program, through `miller_with_solvers`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern)

/-- Plugging keeps an equation determinate. -/
theorem atContext_determinate {S : Signature} {sort : S.Srt} (grammar : ContextGrammar S sort)
    {Γ Δ : Ctx S} (context : grammar.Context Γ Δ) (e : Equation S Δ sort) (determinate : Determinate e) :
    Determinate (atContext grammar context e) := by
  intro W target first second call firstMatch secondMatch
  have firstPlugged : grammar.plug target context (instantiate first e.lhs) = Rigid.includeTerm target call :=
    (grammar.instantiate_plug first context e.lhs).symm.trans firstMatch
  have secondPlugged : grammar.plug target context (instantiate second e.lhs) = Rigid.includeTerm target call :=
    (grammar.instantiate_plug second context e.lhs).symm.trans secondMatch
  obtain ⟨inner, rfl, firstRead⟩ := grammar.plug_recovers context _ call firstPlugged
  have secondRead : instantiate second e.lhs = Rigid.includeTerm target inner :=
    grammar.plug_injective target context
      (secondPlugged.trans (grammar.plug_include target context inner).symm)
  exact (grammar.instantiate_plug first context e.rhs).trans
    ((congrArg (grammar.plug target context) (determinate target first second inner firstRead secondRead)).trans
      (grammar.instantiate_plug second context e.rhs).symm)

namespace Nested

open LambdaContextualRung (sig)
open LambdaComparison (app_inj lam_inj)

theorem beta_determinate (Δ : Ctx sig) : Determinate (betaEquation Δ) := by
  intro W target first second call firstMatch secondMatch
  have both := ((instantiate_beta_lhs first).symm.trans firstMatch).trans
    ((instantiate_beta_lhs second).symm.trans secondMatch).symm
  have parts := app_inj both
  exact (instantiate_beta_rhs first).trans
    ((congrArg₂ inst (lam_inj parts.1) parts.2).trans (instantiate_beta_rhs second).symm)

/-- **β along runs with the actual solver.** Runs of the four-rule λ step are exactly the
readings of runs of the core in λ contexts with a completed incremental solver result at every
firing. -/
theorem lambda_with_solvers {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (LambdaContextualRung.Step Γ) call answer ↔
      ∃ (state : State (contextProgram grammar (betaSchema Γ))) (cache : Cache state),
        SolverPath call state cache ∧ Reads (contextProgram grammar (betaSchema Γ)) state answer := by
  have same : LambdaContextualRung.Step Γ = CRewrites grammar (betaSchema Γ) := by
    funext first second
    exact propext (lambda_rewrites_iff first second).symm
  rw [same, ← context_runs_iff]
  exact execution_with_solvers_iff (fun key => atContext_determinate grammar key.2.1 _ (beta_determinate key.1))
    (fun key => atContext_pattern key.2.1 _ (beta_lhs_pattern key.1)) call answer

end Nested

namespace Quoted

open QuotedLambda (sig)
open QuotedLambdaExecution (Kind app_inj lam_inj quote_inj activate_inj)

theorem family_determinate (Δ : Ctx sig) (kind : Kind) : Determinate (family Δ kind) := by
  cases kind with
  | beta =>
      intro W target first second call firstMatch secondMatch
      have both := ((instantiate_beta_lhs first).symm.trans firstMatch).trans
        ((instantiate_beta_lhs second).symm.trans secondMatch).symm
      have parts := app_inj both
      exact (instantiate_beta_rhs first).trans
        ((congrArg₂ inst (lam_inj parts.1) parts.2).trans (instantiate_beta_rhs second).symm)
  | activation =>
      intro W target first second call firstMatch secondMatch
      have opened : ∀ change : Assignment (activationEquation Δ).arity target,
          instantiate change (activationEquation Δ).lhs =
            QuotedLambdaExecution.activate target (QuotedLambdaExecution.quote target (change ())) :=
        fun change => congrArg (fun code => QuotedLambdaExecution.activate target (QuotedLambdaExecution.quote target code))
          (instantiate_generator change ())
      have both := ((opened first).symm.trans firstMatch).trans ((opened second).symm.trans secondMatch).symm
      exact (instantiate_generator first ()).trans
        ((quote_inj (activate_inj both)).trans (instantiate_generator second ()).symm)

/-- **The quoted-λ account along runs with the actual solver.** -/
theorem quoted_with_solvers {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (QuotedLambda.Step Γ) call answer ↔
      ∃ (state : State (contextProgram grammar (schema Γ))) (cache : Cache state),
        SolverPath call state cache ∧ Reads (contextProgram grammar (schema Γ)) state answer := by
  have same : QuotedLambda.Step Γ = CRewrites grammar (schema Γ) := by
    funext first second
    exact propext (quoted_rewrites_iff first second).symm
  rw [same, ← context_runs_iff]
  exact execution_with_solvers_iff
    (fun key => atContext_determinate grammar key.2.1 _ (family_determinate key.1 key.2.2))
    (fun key => atContext_pattern key.2.1 _ (family_lhs_pattern key.1 key.2.2)) call answer

end Quoted

namespace Controls

open LambdaContextualRung (sig)

theorem lhsSplit_pattern : Pattern sig splitEquation.arity splitEquation.lhs :=
  .rigid (S := sig) LambdaContextualRung.Op.app _
    (.cons _ _ (.object _) (.cons _ _ (.rigid (S := sig) LambdaContextualRung.Op.lam _
      (.cons _ _ (.rigid (S := sig) LambdaContextualRung.Op.app _
        (.cons _ _ (ContextualPatternFragment.generator_pattern _)
          (.cons _ _ (ContextualPatternFragment.generator_pattern _) .nil))) .nil)) .nil))

/-- The two-branch program, along runs: both equations are range-restricted Miller patterns, so every
firing of every run has a completed incremental solver result. -/
theorem two_answers_with_solvers (answer : Term sig Consts .term) :
    Relation.ReflTransGen (Rewrites twoProgram) callEta answer ↔
      ∃ (state : State twoProgram) (cache : Cache state), SolverPath callEta state cache ∧
        Reads twoProgram state answer := by
  refine miller_with_solvers (fun rule => ?_) (fun rule => ?_) callEta answer
  · cases rule with
    | true => exact lhsEta_pattern
    | false => exact lhsSplit_pattern
  · cases rule with
    | true => show ∀ hole ∈ support rhsEta, hole ∈ support lhsEta; decide
    | false => show ∀ hole ∈ support rhsSplit, hole ∈ support lhsSplit; decide

end Controls

#print axioms Controls.lhsSplit_pattern
#print axioms Controls.two_answers_with_solvers
#print axioms atContext_determinate
#print axioms Nested.beta_determinate
#print axioms Nested.lambda_with_solvers
#print axioms Quoted.family_determinate
#print axioms Quoted.quoted_with_solvers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
