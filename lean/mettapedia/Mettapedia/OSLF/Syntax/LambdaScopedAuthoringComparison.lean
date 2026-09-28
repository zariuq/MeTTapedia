import Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
import Mettapedia.OSLF.Syntax.LambdaFiniteRulePremiseComparison
import Mettapedia.OSLF.Syntax.TermClone

/-!
# From a scoped authored premise to the intrinsic lambda rule

The finite scoped-premise notation is tested against the intrinsically scoped
lambda reduction, at its exact binder context. This comparison uses the real
authored DSL declaration and the established beta and LamCong derivations.
The result concerns this concrete rule instance; a general compiler from
arbitrary authored declarations to intrinsic rule polynomials is separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.BinderLocalPremise
open Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
open Mettapedia.GSLT.Examples.ScopedPremiseAuthoring
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Read intrinsic lambda terms as canonical authored patterns, preserving
the de Bruijn index at every binder depth. -/
def wrapBinders (binders : List Srt) (body : Pattern) : Pattern :=
  binders.foldr (fun _ result => .lambda none result) body

mutual

def encodeTerm : {Γ : Ctx sig} → {s : Srt} → Term sig Γ s → Pattern
  | _, _, .var v => .bvar (varIdx v).val
  | _, _, .op .app args => .apply "App" (encodeArgs args)
  | _, _, .op .lam args => .apply "Lam" (encodeArgs args)

def encodeArgs : {arity : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig arity Γ → List Pattern
  | _, _, .nil => []
  | _, _, .cons (bs := binders) head tail =>
      wrapBinders binders (encodeTerm head) :: encodeArgs tail

end

def openRedex : Term sig [Srt.term] .term :=
  appT (lamT (.var .zero)) (.var .zero)

def openTarget : Term sig [Srt.term] .term := .var .zero

/-- The DSL premise's source is the open beta redex under its one binder. -/
theorem source_is_encoded_open_beta :
    dslBodyStep.source = encodeTerm openRedex := by
  rfl

/-- The DSL premise's target is precisely the same local variable. -/
theorem target_is_encoded_open_beta :
    dslBodyStep.target = encodeTerm openTarget := by
  rfl

/-- The authored rule endpoints differ from intrinsic syntax only by inert
surface binder names; erasure gives the exact intrinsic lambda terms. -/
theorem authored_endpoints_encode :
    authoredRule.left.eraseBinderMetadata =
        encodeTerm (lamT openRedex) ∧
      authoredRule.right.eraseBinderMetadata =
        encodeTerm (lamT openTarget) := by
  constructor <;>
    simp [authoredRule, lambdaScoped,
      LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith,
      LanguageDef.nullaryLabels, LanguageDef.ofCore,
      RewriteRule.resolveNullary, Pattern.resolveNullary,
      Pattern.resolveNullaryList, Pattern.eraseBinderMetadata,
      lamT, appT, encodeTerm, encodeArgs, wrapBinders,
      varIdx, openRedex, openTarget]

/-- The source declaration corresponds to a genuine binder-local reduction
and the enclosing LamCong step, retaining the open beta witness. -/
theorem authored_lamCong_has_intrinsic_firing :
    authoredRule.premises = [.scopedStep dslBodyStep] ∧
    Holds Lambda.relation (Lambda.lamCongPremise openRedex openTarget) ∧
    LambdaContextualRung.Step [] (lamT openRedex) (lamT openTarget) := by
  exact ⟨authored_rule_is_scoped,
    Lambda.open_beta_holds,
    closed_step_from_open_body⟩

/-- The corresponding free proof-relevant rule tree keeps the open child;
the existential relation alone would forget this firing evidence. -/
theorem authored_lamCong_has_rule_tree :
    Nonempty (Derivation (lamT openRedex) (lamT openTarget)) := by
  exact step_iff_derivation.mp authored_lamCong_has_intrinsic_firing.2.2

/-- The concrete authored LamCong has a checked scoped premise, exact
intrinsic endpoints, and a retained derivation at those endpoints. -/
theorem authored_lamCong_corresponds :
    lambdaScoped.validate = [] ∧
    (compileRulePremises? lambdaScoped authoredRule =
      some [.step dslBodyStep]) ∧
    dslBodyStep.source = encodeTerm openRedex ∧
    dslBodyStep.target = encodeTerm openTarget ∧
    authoredRule.left.eraseBinderMetadata =
      encodeTerm (lamT openRedex) ∧
    authoredRule.right.eraseBinderMetadata =
      encodeTerm (lamT openTarget) ∧
    Holds Lambda.relation (Lambda.lamCongPremise openRedex openTarget) ∧
    Nonempty (Derivation (lamT openRedex) (lamT openTarget)) := by
  exact ⟨authored_rule_valid, authored_rule_compiles,
    source_is_encoded_open_beta, target_is_encoded_open_beta,
    authored_endpoints_encode.1, authored_endpoints_encode.2,
    authored_lamCong_has_intrinsic_firing.2.1,
    authored_lamCong_has_rule_tree⟩

end Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
