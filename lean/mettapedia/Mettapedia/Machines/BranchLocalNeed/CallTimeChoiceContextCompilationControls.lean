import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceContextCompilation
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceCompositionControls

/-!
# Controls for source-context compilation

The variable-offset controls distinguish compilation underneath source
binders from compiling the hole in its outer environment. Quotation compiles
homomorphically even though semantic replacement under quotation is not
licensed by equality of completed evaluations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.ContextCompilation.Controls

def activateQuotedEvent : Source := .activate (.quote (.emit 11 .hole))

theorem explicit_quote_activation_context :
    activateQuotedEvent.compile .need id =
      .seqFirst (.quote (.emit 11 .hole)) (.seq (.force (.var 0)) (.run (.var 0))) := rfl

theorem quotation_compiles_the_supplied_syntax :
    ((Source.quote .hole).plug (.emit 11 (.con 7 .nil))).toCore .need id =
      .quote (.emit 11 (.ret (.sym 7))) := rfl

theorem compiled_quote_activation_executes_its_captured_event :
    (run [] 40 (.eval Store.empty []
      ((activateQuotedEvent.compile .need id).plug
        ((Expr.con 7 .nil).toCore .need (activateQuotedEvent.holeRenaming id))))).map
        (fun results => results.map fun result => (result.1, result.2.trace)) =
      some [(.ok (.sym 7), [11])] := by
  decide +kernel

/-- The second argument is compiled after one first-argument binder. -/
def secondArgument : Source :=
  .call 5 (.tail (.emit 11 (.con 7 .nil)) (.head .hole .nil))

theorem need_call_argument_wrappers :
    secondArgument.compile .need id =
      .needBody (.emit 11 (.ret (.sym 7)))
        (.needFirst .hole (.call 6 [.var 1, .var 0])) := by
  decide +kernel

theorem value_call_argument_wrappers :
    secondArgument.compile .value id =
      .seqRest (.emit 11 (.ret (.sym 7)))
        (.seqFirst .hole (.call 6 [.var 1, .var 0])) := by
  decide +kernel

theorem name_call_argument_wrappers :
    secondArgument.compile .name id =
      .delayBody (.emit 11 (.ret (.sym 7)))
        (.delayFirst .hole (.call 6 [.var 1, .var 0])) := by
  decide +kernel

theorem earlier_argument_shifts_the_hole : secondArgument.holeRenaming id 0 = 1 := rfl

theorem omitting_the_argument_shift_changes_the_program :
    (secondArgument.plug (.var 0)).toCore .need id ≠
      (secondArgument.compile .need id).plug ((Expr.var 0).toCore .need id) := by
  decide +kernel

/-- Two matched fields and the scrutinee are bound above the outer context;
then one preceding call argument adds another core binder. -/
def nestedBindings : Source :=
  .caseHit (.con 7 .nil) 7 2
    (.call 5 (.tail (.con 0 .nil) (.head .hole .nil))) (.con 9 .nil)

theorem case_fields_are_local_and_outer_variables_are_shifted :
    nestedBindings.holeRenaming (fun index => index + 10) 0 = 1 ∧
    nestedBindings.holeRenaming (fun index => index + 10) 1 = 2 ∧
    nestedBindings.holeRenaming (fun index => index + 10) 2 = 3 ∧
    nestedBindings.holeRenaming (fun index => index + 10) 3 = 14 := by
  decide +kernel

theorem omitting_case_and_argument_binders_changes_the_program :
    (nestedBindings.plug (.var 0)).toCore .need (fun index => index + 10) ≠
      (nestedBindings.compile .need (fun index => index + 10)).plug
        ((Expr.var 0).toCore .need (fun index => index + 10)) := by
  decide +kernel

def primitiveArgument : Source :=
  .prim (.eq 1 0) (.tail (.con 7 .nil) (.head .hole .nil))

theorem primitive_arguments_keep_strict_normalization_in_need_mode :
    primitiveArgument.compile .need id =
      .seqRest (normalized (.ret (.sym 7)))
        (.seqFirst (.seqFirst .hole (.call normHead [.var 0]))
          (.prim (.eq 1 0) [.var 1, .var 0])) := by
  decide +kernel

/-- Compilation under stored code and evaluation-equivalence substitution
under stored code are different laws. The latter remains false. -/
theorem quotation_is_not_a_semantic_replacement_context :
    Composition.Equivalent [] Composition.Controls.discarded (.ret (.sym 2)) ∧
      ¬ Composition.Equivalent [] (.quote Composition.Controls.discarded)
        (.quote (.ret (.sym 2))) :=
  ⟨Composition.Controls.discard_pure_stage [],
    Composition.Controls.stored_code_is_a_stronger_observer []⟩

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.ContextCompilation.Controls
