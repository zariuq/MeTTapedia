import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramGuards

/-!
# Body admission is exactly one constructed native firing

For every compiled body and every producer of it, the compiler constructs
the rule, physical selection, output syntax, publication flags and
resource/guard queries. The comparison assumes neither successful source
admission nor source shape/resource validity. Those obligations are
checked by the compiled queries. The native firing includes an actual
worklist return at the declared finite budget.

This is admission equivalence for the constructed entry/control context.
Result observations depend on each clause kind's publication contract;
arbitrary program contexts have their separate obligations, and the
control occurrence is explicit program data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

namespace Producer

variable {body : Body S O Γ sort before after} (producer : body.Producer)

/-- The resource queries and every original-cut guard query of the producer's firing. -/
noncomputable def queries (occupied : Finset Nat) :=
  body.producerResourceQueries ++ body.producerGuardQueries occupied producer.values

theorem source_iff_native_body_admission
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    body.Admitted ↔
      ∃ observed : WithQueries body.guardNativeBank (body.nativeBindingState occupied),
        observed.firing.rule = producer.rule ∧ observed.firing.selection = body.bindingSelection ∧
          observed.firing.outputs = producer.outputs occupied ∧ observed.firing.reusable = producer.reusable ∧
          observed.firing.fuel = fuel ∧ observed.queries = producer.queries occupied := by
  constructor
  · intro source
    obtain ⟨shapes, resources, consistent, guards⟩ := body.admitted_iff.mp source
    obtain ⟨firing, rule, selection, outputs, reusable, budget⟩ :=
      producer.realize shapes resources consistent occupied fuel
    have nativeConsistent :=
      (body.native_binding_solvable_iff shapes resources occupied producer.values []).mpr consistent
    have structural := (body.producer_resource_queries_iff occupied producer.values nativeConsistent).mpr
      ⟨shapes, resources⟩
    have checked := (body.producer_guard_queries_iff shapes resources consistent occupied producer.values).mp guards
    have observations : ∀ query ∈ producer.queries occupied,
        AskData (ContextualConditionalExecution.information body.guardNativeBank body.guardFamily occupied
          firing.selection firing.rule (body.nativeBindingState occupied).rows (body.nativeBindingState occupied).equations)
          query (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present := by
      intro query member
      rw [rule, selection]
      rcases List.mem_append.mp member with resource | guard
      · exact structural query resource
      · exact checked query guard
    let observed : WithQueries body.guardNativeBank (body.nativeBindingState occupied) :=
      ⟨firing, producer.queries occupied, observations⟩
    exact ⟨observed, rule, selection, outputs, reusable, budget, rfl⟩
  · rintro ⟨observed, rule, selection, _outputs, _reusable, _budget, queries⟩
    have nativeConsistent : ContextualConditionalExecution.Solvable
        (body.nativeBindingInformation occupied producer.values []) := by
      have original := observed.firing.admitted.solvable
      rw [rule, selection] at original
      exact original
    have observations : ∀ query ∈ producer.queries occupied,
        AskData (body.nativeBindingInformation occupied producer.values []) query
          (nativeLabels body.guardNativeBank (body.nativeBindingState occupied))
          (body.nativeBindingState occupied).present := by
      intro query member
      have original := observed.observations query (by rw [queries]; exact member)
      rw [rule, selection] at original
      exact original
    have structural := (body.producer_resource_queries_iff occupied producer.values nativeConsistent).mp
      (fun query member => observations query (List.mem_append_left _ member))
    obtain ⟨shapes, resources⟩ := structural
    have consistent :=
      (body.native_binding_solvable_iff shapes resources occupied producer.values []).mp nativeConsistent
    have guards := (body.producer_guard_queries_iff shapes resources consistent occupied producer.values).mpr
      (fun query member => observations query (List.mem_append_right _ member))
    exact body.admitted_iff.mpr ⟨shapes, resources, consistent, guards⟩

end Producer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
