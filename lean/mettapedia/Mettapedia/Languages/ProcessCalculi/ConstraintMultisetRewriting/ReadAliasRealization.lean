import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourceLifting

/-! # The realized physical read quotient preserves prototype alias classes -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning.ReadRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {assignment : S} {label : O → T} {rule : RuleInstance T}
  {plan : ReadPlan A assignment label rule} {actual : Selection O}

def port (realization : ReadRealization A assignment label plan actual)
    (index : Fin plan.prototype.length) : O :=
  actual.read.get (Fin.cast realization.read_length.symm index)

theorem port_value (realization : ReadRealization A assignment label plan actual)
    (index : Fin plan.prototype.length) : realization.port index = realization.embedding (plan.portClass index) := by
  simp only [port, realization.ports, List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast]

theorem actual_alias_iff (realization : ReadRealization A assignment label plan actual)
    (first second : Fin plan.prototype.length) :
    realization.port first = realization.port second ↔
      plan.prototype.get first = plan.prototype.get second := by
  rw [realization.port_value, realization.port_value]
  exact realization.alias_iff first second

theorem actual_gluing {before : Configuration T O} (valid : actual.Valid A label rule before) :
    IsPushout
      (↾(Sum.inr : ReadPortPushouts.Port actual.read →
        ReadPortPushouts.Port actual.taken ⊕ ReadPortPushouts.Port actual.read))
      (↾(ReadPortPushouts.readQuotient actual)) (↾(ReadPortPushouts.quotientLeft actual))
      (↾(ReadPortPushouts.supportRead actual)) :=
  ReadPortPushouts.read_gluing_pushout actual (OccurrenceIdentification.valid_identification valid)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning.ReadRealization
