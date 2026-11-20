import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationIntrinsicBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationBindingApplication
import Mettapedia.OSLF.Syntax.BindingSignatureABTSubstitution

/-!
# Binding application through the authored transform representation

The same physical ABT graft is used by intrinsic binding terms and authored
contextual values. For intrinsic arguments, grafting the represented trees and
reading the result computes the capture-avoiding intrinsic application. For
authored values, the physical operation preserves and reflects the existing
source application's answers and refusals. Binder display names are observed
only modulo the source's alpha equivalence.

These statements concern the existing scoped graft, head presentations and
source application. They introduce no new term carrier or evaluation policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef

namespace Syntax

section Intrinsic

variable {S : Signature} [DecidableEq S.Srt]

/-- Execute the common physical application and check the returned intrinsic
sort and context, using the selected head presentation. -/
def graftAndRead? (code : Presentation.Intrinsic.HeadPresentation S)
    (context : Ctx S) (sort : S.Srt) (arity : Nat)
    (arguments : List Presentation.Payloads.Term) (body : Presentation.Payloads.Term) :
    Option (Term S context sort) := do
  let result ← SignatureIndexedABT.ScopedApplication.graft arity arguments body
  Presentation.Intrinsic.read? code context sort result

omit [DecidableEq S.Srt] in
/-- The physical result is the representation of intrinsic application; in
particular, nested binders are traversed by the existing capture-avoiding graft. -/
theorem intrinsic_graft (code : Presentation.Intrinsic.HeadPresentation S)
    {parameters context : Ctx S} {sort : S.Srt}
    (body : Term S parameters sort)
    (arguments : Args S (parameters.map (fun parameter => ([], parameter))) context) :
    SignatureIndexedABT.ScopedApplication.graft parameters.length
      ((CommonABT.lowerSpine arguments).map (SignatureIndexedABT.mapHeads (code.view (sort := ()))))
      (Presentation.Intrinsic.lower code body) =
      some (Presentation.Intrinsic.lower code (bind (argsToSub arguments) body)) := by
  rw [Presentation.Intrinsic.lower, SignatureIndexedABT.graft_mapHeads,
    CommonABT.graft_lower]
  rfl

/-- This checks the actual physical result, rather than applying intrinsic
substitution first and merely printing it. -/
theorem intrinsic_application_readback (code : Presentation.Intrinsic.HeadPresentation S)
    {parameters context : Ctx S} {sort : S.Srt}
    (body : Term S parameters sort)
    (arguments : Args S (parameters.map (fun parameter => ([], parameter))) context) :
    graftAndRead? code context sort parameters.length
      ((CommonABT.lowerSpine arguments).map (SignatureIndexedABT.mapHeads (code.view (sort := ()))))
      (Presentation.Intrinsic.lower code body) = some (bind (argsToSub arguments) body) := by
  unfold graftAndRead?
  rw [intrinsic_graft]
  exact Presentation.Intrinsic.read_lower code _

theorem intrinsic_application_exact (code : Presentation.Intrinsic.HeadPresentation S)
    {parameters context : Ctx S} {sort : S.Srt}
    (body : Term S parameters sort)
    (arguments : Args S (parameters.map (fun parameter => ([], parameter))) context)
    (result : Term S context sort) :
    graftAndRead? code context sort parameters.length
      ((CommonABT.lowerSpine arguments).map (SignatureIndexedABT.mapHeads (code.view (sort := ()))))
      (Presentation.Intrinsic.lower code body) = some result ↔
      bind (argsToSub arguments) body = result := by
  rw [intrinsic_application_readback, Option.some.injEq]

/-- Physical arity refusal occurs before readback and cannot acquire a
well-typed result from an interpretation of the head symbols. -/
theorem wrong_arity_refused (code : Presentation.Intrinsic.HeadPresentation S)
    (context : Ctx S) (sort : S.Srt) (arity : Nat)
    (arguments : List Presentation.Payloads.Term) (body : Presentation.Payloads.Term)
    (different : arguments.length ≠ arity) :
    graftAndRead? code context sort arity arguments body = none := by
  simp [graftAndRead?, SignatureIndexedABT.ScopedApplication.graft, different]

end Intrinsic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding

/-- The target result need agree with a requested source result only up to
the authored pattern language's own alpha equivalence. -/
theorem authored_application_exact (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern) :
    Presentation.Binding.instantiateContextual? value ambient depth arguments =
        some (Presentation.Binding.lowerPattern result) ↔
      ∃ source, instantiateValue? value ambient depth arguments = some source ∧
        source.AlphaEquiv result := by
  rw [Presentation.Binding.source_success_iff]
  simp only [Presentation.Binding.lowerPattern_eq_iff_alpha]

/-- All authored scope and arity refusals survive the physical application.
This is an application refusal, not a general unification refutation. -/
theorem authored_application_refusal (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) :
    Presentation.Binding.instantiateContextual? value ambient depth arguments = none ↔
      instantiateValue? value ambient depth arguments = none :=
  Presentation.Binding.source_refusal_iff value ambient depth arguments

theorem authored_application_scoped (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (applied : Presentation.Binding.instantiateContextual? value ambient depth arguments =
      some (Presentation.Binding.lowerPattern result)) :
    result.isWellScopedAt (depth + ambient) = true := by
  have supported := Presentation.Binding.result_scoped value ambient depth arguments applied
  rwa [Presentation.Binding.lowerPattern_scope] at supported

namespace Controls

/-- One dependency crosses an inner lambda while a distinct ambient variable
remains outside it. The metadata name of the inner binder is irrelevant. -/
theorem nested_capture_avoiding_application :
    Presentation.Binding.instantiateContextual? Presentation.Binding.Controls.nested 1 1 [.bvar 0] =
      some (Presentation.Binding.lowerPattern
        (.lambda (some "renamed") (.apply "pair" [.bvar 1, .bvar 2]))) := by
  rw [Presentation.Binding.Controls.nested_application]
  exact congrArg some (Presentation.Binding.alpha_renamed_binder_agrees _ _ _)

theorem nested_result_is_scoped :
    (Pattern.lambda (some "renamed") (.apply "pair" [.bvar 1, .bvar 2])).isWellScopedAt 2 = true :=
  authored_application_scoped Presentation.Binding.Controls.nested 1 1 [.bvar 0] _
    nested_capture_avoiding_application

theorem escaped_argument_does_not_apply :
    instantiateValue? RuleBindingABT.Controls.value 1 1 [.bvar 2] = none :=
  (authored_application_refusal _ _ _ _).mp Presentation.Binding.Controls.escaped_argument_refused

theorem missing_dependency_does_not_apply :
    instantiateValue? RuleBindingABT.Controls.value 1 1 [] = none :=
  (authored_application_refusal _ _ _ _).mp Presentation.Binding.Controls.missing_dependency_refused

end Controls

end Syntax

#print axioms Syntax.intrinsic_application_readback
#print axioms Syntax.intrinsic_application_exact
#print axioms Syntax.authored_application_exact
#print axioms Syntax.Controls.nested_capture_avoiding_application

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration
