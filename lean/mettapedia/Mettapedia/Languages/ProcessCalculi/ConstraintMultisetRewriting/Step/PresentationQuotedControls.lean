import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationQuotedSource

/-!
# Source quotation controls with captures and explicit activation

Lexically captured variables survive a nested binder. A reducible quoted body
remains inert until activation, and one activation removes one quotation.
Malformed binder fields and confusion with opaque rule handles are separate
readback refusals in this named profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedSource.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open QuotedLambda (sig)
open QuotedLambda.Controls
open LambdaContextualRung (Srt)

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

theorem named_code_then_activation :
    Relation.ReflTransGen (Reduces []) (source quotedArgumentProgram) (source identity) :=
  preserves_run passing_named_code_then_explicitly_activating

theorem nested_binder_capture_preserved :
    Relation.ReflTransGen (Reduces [.term]) (source capturedProgram) (source capturedResult) :=
  preserves_run activation_retains_a_capture_beneath_an_inner_lambda

theorem captured_source_is_not_the_inner_variable :
    source capturedResult ≠ source (QuotedLambda.lam (.var .zero) : Term sig [.term] .term) := by
  intro same
  have read := congrArg (read? [.term]) same
  rw [read_source, read_source] at read
  exact the_result_did_not_capture_the_inner_binder (Option.some.inj read)

theorem quoted_loop_has_no_step (output : List Nat) :
    ¬ Reduces [] (source (QuotedLambda.quote looping)) output := quotation_inert looping output

theorem explicit_activation_exposes_loop :
    Reduces [] (source (QuotedLambda.activate (QuotedLambda.quote looping))) (source looping) :=
  explicit_activation looping

theorem unquoted_loop_does_step : Reduces [] (source looping) (source looping) :=
  (encoded_reduction_iff _ _).mpr the_unquoted_body_can_reduce_forever_one_step_at_a_time

theorem one_quote_at_a_time :
    Reduces [] (source (QuotedLambda.activate (QuotedLambda.quote (QuotedLambda.quote looping))))
      (source (QuotedLambda.quote looping)) ∧
    ∀ output, ¬ Reduces [] (source (QuotedLambda.quote looping)) output :=
  ⟨explicit_activation (QuotedLambda.quote looping), quoted_loop_has_no_step⟩

def malformedLambda : Payloads.Term := .node (.symbol 1) (.cons 0 (.idx 0) .nil)

theorem wrong_binder_depth_refused : Intrinsic.read? code [] .term malformedLambda = none := by
  decide +kernel

theorem opaque_rule_handle_is_not_lexical_quote (handle : Nat) :
    Intrinsic.read? code [] .term (.node (.quotedRule handle) .nil) = none := rfl

theorem active_substitution_retains_lexical_captures {Γ Δ : Ctx sig}
    (assignment : Sub sig Γ Δ) (body : Term sig Γ .term) :
    read? Δ (source (bind assignment (QuotedLambda.quote body))) =
      some (QuotedLambda.quote (bind assignment body)) :=
  read_source _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedSource.Controls
