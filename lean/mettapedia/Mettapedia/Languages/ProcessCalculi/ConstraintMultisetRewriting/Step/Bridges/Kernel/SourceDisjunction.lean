import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics

/-!
# The source disjunction used by native case equations

HOL Light defines disjunction by universal elimination into a proposition.
This reader checks that defining equation in the received cache and derives
its ordinary disjunction meaning in the constructed source model. No
uninterpreted symbol named disjunction is silently assigned that meaning.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDisjunction

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open ReferenceBooleanSemantics ProofExecution TypeFamilySemantics

universe w

abbrev Operator := HOL.ClosedTerm Symbol (HOL.Ty.arr .prop (HOL.Ty.arr .prop .prop))

def body : Operator :=
  .lam (.lam (universal (type := .prop)
    (implication (implication (.var (.vs (.vs .vz))) (.var .vz))
      (implication (implication (.var (.vs .vz)) (.var .vz)) (.var .vz)))))

def equation (operation : Operator) : HOL.ClosedFormula Symbol := .eq operation body

def empty (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : model.Valuation [] :=
  fun index => nomatch index

theorem empty_unique (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (valuation : model.Valuation []) : @valuation = @empty model := by
  funext type index
  exact nomatch index

theorem body_meaning (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model) (left right : ULift.{w+1} Prop) :
    (model.denote body (empty model) left right).down ↔ left.down ∨ right.down := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [body, HOL.HenkinModel.denote, HOL.PreModel.denote,
    denote_universal model meanings, denote_implication model meanings,
    HOL.PreModel.extend, admitted, forall_true_left, ULift.down_up]
  constructor
  · intro all
    exact all (ULift.up (left.down ∨ right.down)) Or.inl Or.inr
  · intro holds result fromLeft fromRight
    exact holds.elim fromLeft fromRight

theorem equation_meaning (operation : Operator)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model)
    (valid : model.models (equation operation)) (left right : ULift.{w+1} Prop) :
    (model.denote operation (empty model) left right).down ↔ left.down ∨ right.down := by
  have same : model.denote operation (empty model) = model.denote body (empty model) := by
    have original := valid
    simp only [equation, HOL.HenkinModel.models, HOL.PreModel.models,
      HOL.PreModel.denote,
      model.eqv_iff_eq_of_fullDomains full, empty_unique model] at original
    exact original
  rw [same]
  exact body_meaning model full meanings left right

theorem received_meaning (operation : Operator)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : ExactFormulaReadback.ReadFact state (equation operation))
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ left right : ULift.{w+1} Prop,
      (model.denote operation (empty model) left right).down ↔ left.down ∨ right.down := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  exact equation_meaning operation (frame.model other assignment)
    (frame.model_fullDomains other assignment)
    (replay_meanings commands state accepted other assignment)
    (ExactFormulaReadback.read_models frame other assignment _ reading)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDisjunction
