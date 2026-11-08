import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationExecution

/-!
# Publication intent belongs to the produced ports

Fresh occurrence allocation must not choose whether an output is reusable
or shared. A plan declares one intent per production port, and the selected
fresh identities receive those intents in the same order. The allocation
map preserves the declared list and commutes with injective identity changes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

variable {T O P : Type} [DecidableEq O]

structure Plan (T : Type) where
  rule : RuleInstance T
  reusable : List Bool
  shape : reusable.length = rule.produce.length

def flagsFor : List O → List Bool → O → Bool
  | first :: rest,kind :: kinds,occurrence => if occurrence = first then kind else flagsFor rest kinds occurrence
  | _,_,_ => false

theorem flagsFor_map : ∀ (occurrences : List O) (kinds : List Bool),
    occurrences.Nodup → occurrences.length = kinds.length → occurrences.map (flagsFor occurrences kinds) = kinds
  | [],[],_,_ => rfl
  | [],_ :: _,_,lengths => by cases lengths
  | _ :: _,[],_,lengths => by cases lengths
  | first :: rest,kind :: kinds,unique,lengths => by
      simp only [List.map_cons,flagsFor,ite_true]
      have restEqual : rest.map (fun occurrence => if occurrence = first then kind else flagsFor rest kinds occurrence) =
          rest.map (flagsFor rest kinds) := by
        apply List.map_congr_left
        intro occurrence member
        have different : occurrence ≠ first := by
          intro same
          exact (List.nodup_cons.mp unique).1 (same ▸ member)
        exact if_neg different
      rw [restEqual,flagsFor_map rest kinds (List.nodup_cons.mp unique).2 (Nat.succ.inj lengths)]

theorem flagsFor_rename [DecidableEq P] (change : O → P) (injective : Function.Injective change) :
    ∀ (occurrences : List O) (kinds : List Bool) (occurrence : O),
      flagsFor (occurrences.map change) kinds (change occurrence) = flagsFor occurrences kinds occurrence
  | [],_,_ => rfl
  | _ :: _,[],_ => rfl
  | first :: rest,kind :: kinds,occurrence => by
      simp only [List.map_cons,flagsFor,injective.eq_iff]
      split
      · rfl
      · exact flagsFor_rename change injective rest kinds occurrence

variable {S : Mettapedia.OSLF.Binding.Signature} {Local : Type}
    (locals : Local → Mettapedia.OSLF.Binding.MetaArity S)
    [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

theorem realize_planned_publication {Γ : Ctx S} {sort : S.Srt}
    (before : ContextualExecution.Endpoint locals O Γ sort)
    (plan : Plan (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (covered : ContextualWorldScopeLedger.RuleCovered (ContextualScopeSupport.privateScopes before.scopes)
      before.occupied plan.rule)
    (admitted : ContextualGuardedStep.Valid locals before.declarations before.occupied
      selection plan.rule before.inventory.rows before.inventory.configuration outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied selection plan.rule
        before.inventory.rows before.inventory.configuration))) :
    ∃ firing : Firing (before := before), firing.rule = plan.rule ∧ firing.selection = selection ∧
      firing.outputs = outputs ∧ selection.made.map firing.reusable = plan.reusable := by
  obtain ⟨firing,ruleEq,selectionEq,outputsEq,kindEq⟩ :=
    realize_publication locals before plan.rule selection outputs
      (flagsFor selection.made plan.reusable) covered admitted patterned
  refine ⟨firing,ruleEq,selectionEq,outputsEq,?_⟩
  rw [kindEq]
  apply flagsFor_map _ _ admitted.output_distinct
  have lengths := congrArg List.length admitted.outputs
  have outputsLength : selection.made.length = plan.rule.produce.length := by
    simpa only [List.length_map,ContextualActivatedStep.prepared,ContextualSelectionViews.prepare,
      ContextualFreshening.ruleAt,RuleInstance.map] using lengths
  exact outputsLength.trans plan.shape.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication
