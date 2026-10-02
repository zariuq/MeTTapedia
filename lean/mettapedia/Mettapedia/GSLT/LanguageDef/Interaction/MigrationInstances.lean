import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction

/-!
# Rho and lambda migrate by binding

In both calculi the contraction substitutes what the environment brought into
the program continuation, through the binder the program introduction
carries.  The cut has the same shape as in a calculus that moves nothing; the
substitution is what the contraction does, not what the cut is.

The lambda calculus also shows what binding means for behaviour: one
abstraction applied to two different arguments leaves two different
residuals, so the residual of the program is not determined by the program.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction

/-- The environment of rho's cut brings the message; the program brings the
body of the input. -/
theorem rho_cut_variables :
    rhoInteractionCut.environmentVariables = ["q"] ∧
      rhoInteractionCut.programVariables = ["p"] := by
  decide +kernel

/-- Rho's contraction substitutes the quoted message into the input body. -/
theorem rho_bindsFromEnvironment : rhoInteractionCut.BindsFromEnvironment := by
  decide +kernel

/-- **Rho migrates by binding.** -/
theorem rho_migrationMode : rhoInteractionCut.migrationMode = .binding :=
  rhoInteractionCut.migrationMode_eq_binding_of_bindsFromEnvironment
    rho_bindsFromEnvironment

/-- The contractum of rho's communication rule is a parallel composition
around a substitution node whose body is the program continuation and whose
replacement mentions the message. -/
theorem rho_binds_through_substitution :
    ∃ (outer inner : OneHoleContext) (replacement : Pattern),
      rhoCommRewrite.right = outer.fill (.subst (inner.fill (.fvar "p")) replacement) ∧
        ∃ source ∈ rhoInteractionCut.environmentVariables,
          source ∈ replacement.freeFvarNames :=
  exists_subst_of_bindsInto rho_bindsFromEnvironment

/-- Beta substitutes the argument into the abstraction body. -/
theorem lambda_bindsFromEnvironment : lambdaInteractionCut.BindsFromEnvironment := by
  decide +kernel

/-- **Lambda migrates by binding.** -/
theorem lambda_migrationMode : lambdaInteractionCut.migrationMode = .binding :=
  lambdaInteractionCut.migrationMode_eq_binding_of_bindsFromEnvironment
    lambda_bindsFromEnvironment

/-- Application is a free binary contact: the subject of beta is carried by
position, with no explicit term to match. -/
theorem lambda_subject_structural :
    lambdaInteractionCut.program.subject.pattern = none ∧
      lambdaInteractionCut.environment.subject.pattern = none ∧
        ContactEquationFree lambdaInteractivePresentation := by
  refine ⟨rfl, rfl, ?_⟩
  intro equation membership
  cases membership

/-- Rho's subject is carried nominally: the same name on both sides. -/
theorem rho_subject_nominal :
    rhoInteractionCut.program.subject.pattern = some (.fvar "n") ∧
      rhoInteractionCut.environment.subject.pattern = some (.fvar "n") :=
  ⟨rfl, rfl⟩

/-! ## What binding does to behaviour -/

/-- The identity abstraction. -/
def lambdaIdentity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]

/-- The first projection. -/
def lambdaFirst : Pattern :=
  .apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.bvar 1)])]

/-- The identity applied to itself reduces to the identity. -/
theorem lambda_identity_on_identity :
    Step defaultBasePremises lambdaCalc
      (.apply "App" [lambdaIdentity, lambdaIdentity]) lambdaIdentity :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The identity applied to the first projection reduces to the first
projection. -/
theorem lambda_identity_on_first :
    Step defaultBasePremises lambdaCalc
      (.apply "App" [lambdaIdentity, lambdaFirst]) lambdaFirst :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- One program, two environments, two residuals: what is left of the program
after the contraction depends on what the environment brought. -/
theorem lambda_residual_depends_on_argument :
    ∃ program first second firstResidual secondResidual : Pattern,
      Step defaultBasePremises lambdaCalc (.apply "App" [program, first]) firstResidual ∧
        Step defaultBasePremises lambdaCalc (.apply "App" [program, second])
          secondResidual ∧
          firstResidual ≠ secondResidual :=
  ⟨lambdaIdentity, lambdaIdentity, lambdaFirst, lambdaIdentity, lambdaFirst,
    lambda_identity_on_identity, lambda_identity_on_first, by decide⟩

end Mettapedia.GSLT.LanguageDef
