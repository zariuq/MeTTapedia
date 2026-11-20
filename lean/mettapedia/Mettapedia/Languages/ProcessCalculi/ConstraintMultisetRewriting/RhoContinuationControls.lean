import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuationSealing
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.OSLF.Syntax.RhoQuotationClassFibres

/-!
# Name, activation and sealing controls for compiled rho continuations

The continuation uses the received name as a channel and its active process
under a further input binder. Independent source semantic substitution agrees
on this example. A literal quoted drop remains literal, and a quote crossing
the source's sealed boundary is rejected by its existing admission check.

These controls do not replace a general source-substitution or core-execution
adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open RhoSchema.IntrinsicEncoding
open ContextualCommunication (base operatorEquality)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus (semanticCommSubst)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq RhoSchema.Srt)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := operatorEquality sort

def noMetas : Empty → MetaArity base := Empty.elim

def payload : Term base [] .pr :=
  RhoSchema.ClosedCommunication.output RhoSchema.chan RhoSchema.nilP

/-- The old receiver variable is index one under the new input binder. -/
def body : Term base [.nm] .pr :=
  .op .out (.cons (.var .zero) (.cons
    (.op .inp (.cons (.var .zero) (.cons
      (.op .par (.cons (.op .drp (.cons (.var (.succ .zero)) .nil))
        (.cons (.op .drp (.cons (.var .zero) .nil)) .nil))) .nil))) .nil))

def expected : Term base [] .pr :=
  RhoSchema.ClosedCommunication.output (RhoSchema.ClosedCommunication.quote payload)
    (RhoSchema.ClosedCommunication.input (RhoSchema.ClosedCommunication.quote payload)
      (.op .par (.cons (weaken payload) (.cons (.op .drp (.cons (.var .zero) .nil)) .nil))))

theorem nested_receiver_is_quote_safe : intrinsicQuoteSafe 1 body = true := by decide +kernel

theorem compiled_name_and_active_views :
    continuation body (Rigid.includeTerm noMetas payload) = Rigid.includeTerm noMetas expected := by
  decide +kernel

/-- This invokes the independent source operation, not the compiler. -/
theorem source_semantic_substitution_agrees :
    semanticCommSubst (encodeTerm body) (encodeTerm payload) = encodeTerm expected := by
  decide +kernel

abbrev symbols : Unit → MetaArity base := fun _ => ([], .pr)
def assignment : Assignment symbols noMetas := fun _ => Rigid.includeTerm noMetas payload

theorem actual_contextual_assignment_under_input :
    instantiate assignment (continuation body (generator symbols ())) = Rigid.includeTerm noMetas expected := by
  rw [continuation_instantiate,instantiate_generator]
  exact compiled_name_and_active_views

def literalDrop : Term base [] .pr :=
  .op .drp (.cons (RhoSchema.ClosedCommunication.quote payload) .nil)

theorem literal_drop_is_not_activated :
    continuation (weaken literalDrop) (Rigid.includeTerm noMetas RhoSchema.nilP) =
      Rigid.includeTerm noMetas literalDrop := by
  decide +kernel

theorem literal_drop_is_not_the_payload :
    continuation (weaken literalDrop) (Rigid.includeTerm noMetas RhoSchema.nilP) ≠
      Rigid.includeTerm noMetas payload := by
  decide +kernel

theorem source_also_preserves_literal_drop :
    semanticCommSubst (encodeTerm (weaken (t := RhoSchema.Srt.nm) literalDrop))
      (encodeTerm RhoSchema.nilP) = encodeTerm literalDrop := by
  decide +kernel

def closedCode : Term base [] .pr :=
  RhoSchema.ClosedCommunication.input RhoSchema.chan (.op .drp (.cons (.var .zero) .nil))

theorem quoted_inner_binder_is_sealed :
    compileName (received (Rigid.includeTerm noMetas RhoSchema.nilP))
        (.op .quo (.cons (weaken closedCode) .nil)) =
      compileName (received (Rigid.includeTerm noMetas payload))
        (.op .quo (.cons (weaken closedCode) .nil)) :=
  quoted_code_ignores_environment _ _ _ (by decide +kernel)

theorem quoted_inner_binder_retains_its_code :
    compileName (received (Rigid.includeTerm noMetas payload))
        (.op .quo (.cons (weaken closedCode) .nil)) =
      Rigid.includeTerm noMetas (RhoSchema.ClosedCommunication.quote closedCode) := by
  decide +kernel

def crossingQuote : Term base [.nm] .nm :=
  .op .quo (.cons (.op .drp (.cons (.var .zero) .nil)) .nil)

theorem outer_capture_under_quote_is_rejected : intrinsicQuoteSafe 1 crossingQuote = false := by
  decide +kernel

/-- Omitting the source admission check would admit payload-dependent code. -/
theorem unsafe_quote_depends_on_the_receiver :
    compileName (received (Rigid.includeTerm noMetas RhoSchema.nilP)) crossingQuote ≠
      compileName (received (Rigid.includeTerm noMetas payload)) crossingQuote := by
  decide +kernel

/-! ## Name classes do not determine the received process origin -/

namespace Origins

open Mettapedia.OSLF.Binding.RhoQuotationClassFibres

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open RhoSchema.IntrinsicEncoding

theorem the_two_payloads_are_admitted_intrinsic_sources :
    intrinsicQuoteSafe 0 RhoSourceOutputPredicate.output = true ∧
      intrinsicQuoteSafe 0 suspendedRaw = true := by decide +kernel

theorem the_two_payloads_transmit_equivalent_names :
    NameEquiv (.apply "NQuote" [encodeTerm suspendedRaw])
      (.apply "NQuote" [encodeTerm RhoSourceOutputPredicate.output]) := .quote_drop _

theorem the_two_origins_give_distinct_semantic_results :
    semanticCommSubst (.apply "PDrop" [.bvar 0])
        (encodeTerm RhoSourceOutputPredicate.output) = encodeTerm RhoSourceOutputPredicate.output ∧
      semanticCommSubst (.apply "PDrop" [.bvar 0])
        (encodeTerm suspendedRaw) = encodeTerm suspendedRaw ∧
      ¬ StructuralCongruence (encodeTerm suspendedRaw) (encodeTerm RhoSourceOutputPredicate.output) := by
  refine ⟨rfl, rfl, fun same => ?_⟩
  have keys := Canonical.canonicalize_eq_of_structuralCongruence same
    (by simp [suspendedRaw, dropRaw, quoteRaw, RhoSourceOutputPredicate.output,
      encodeTerm, RhoSchema.IntrinsicEncoding.encodeArgs, wrapBinders, RhoSchema.chan, RhoSchema.nilP,
      Canonical.HashSetFree, Canonical.HashSetFreeList])
    (by simp [RhoSourceOutputPredicate.output, encodeTerm, RhoSchema.IntrinsicEncoding.encodeArgs, wrapBinders,
      RhoSchema.chan, RhoSchema.nilP, Canonical.HashSetFree, Canonical.HashSetFreeList])
  exact (show Canonical.canonicalize (encodeTerm suspendedRaw) ≠
    Canonical.canonicalize (encodeTerm RhoSourceOutputPredicate.output) from by decide +kernel) keys

/-- Respect for name equivalence and recovery of both actual COMM origins
cannot be satisfied by one name-only operation, even up to process equations. -/
theorem no_name_equivariant_activation_realizes_both_origins :
    ¬ ∃ activate : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern,
      (∀ first second, NameEquiv first second → StructuralCongruence (activate first) (activate second)) ∧
      StructuralCongruence
        (activate (.apply "NQuote" [encodeTerm suspendedRaw]))
        (semanticCommSubst (.apply "PDrop" [.bvar 0]) (encodeTerm suspendedRaw)) ∧
      StructuralCongruence
        (activate (.apply "NQuote" [encodeTerm RhoSourceOutputPredicate.output]))
        (semanticCommSubst (.apply "PDrop" [.bvar 0]) (encodeTerm RhoSourceOutputPredicate.output)) := by
  rintro ⟨activate, respects, first, second⟩
  have compared := respects _ _ the_two_payloads_transmit_equivalent_names
  rw [the_two_origins_give_distinct_semantic_results.1] at second
  rw [the_two_origins_give_distinct_semantic_results.2.1] at first
  exact the_two_origins_give_distinct_semantic_results.2.2
    (StructuralCongruence.trans _ _ _ (StructuralCongruence.symm _ _ first)
      (StructuralCongruence.trans _ _ _ compared second))

#print axioms the_two_origins_give_distinct_semantic_results
#print axioms no_name_equivariant_activation_realizes_both_origins

end Origins

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RhoContinuation.Controls
