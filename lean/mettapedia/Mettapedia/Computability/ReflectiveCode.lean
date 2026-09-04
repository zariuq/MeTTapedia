import Mettapedia.TypeTheory.ExtensionalReadout

/-!
# Reflective code: static laws, operational execution, and quotient exactness

Quotation and execution are often written as though they were inverse
functions.  Reflective process calculi show why that is too coarse.  A name
equation may identify `quote (drop name)` with `name`, while executing
`drop (quote process)` is a transition available only in a selected
operational context.  Neither law manufactures the other.

This module separates four pieces of structure:

* the raw quotation/drop interface;
* beta and eta as literal equalities;
* beta and eta relative to independently supplied equivalence relations; and
* beta as a proof-relevant operational step.

Literal beta turns dropping into a split readout from names to processes.
Eta is exactly faithfulness of that readout.  Relative beta and eta instead
yield an equivalence only after quotienting by the selected relations.  An
operational beta becomes literal beta only when the operational step itself
reflects equality.

The definitions do not select a staging calculus, process calculus, syntax
representation, evaluation policy, or product language.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ReflectiveCode

open Mettapedia.TypeTheory.ExtensionalReadout

universe uProcess uName uStep

/-- Raw quotation and dropping operations.  No equation or transition is
included in the interface. -/
structure Interface (Process : Type uProcess) (Name : Type uName) where
  quote : Process -> Name
  drop : Name -> Process

namespace Interface

variable {Process : Type uProcess} {Name : Type uName}

/-- Process beta as literal equality: dropping a quotation recovers the
process. -/
def StaticBeta (interface : Interface Process Name) : Prop :=
  forall process, interface.drop (interface.quote process) = process

/-- Name eta as literal equality: quoting a dropped name recovers the name. -/
def StaticEta (interface : Interface Process Name) : Prop :=
  forall name, interface.quote (interface.drop name) = name

/-- Process beta relative to a selected process relation. -/
def BetaAlong (interface : Interface Process Name)
    (processRel : Process -> Process -> Prop) : Prop :=
  forall process, processRel (interface.drop (interface.quote process)) process

/-- Name eta relative to a selected name relation. -/
def EtaAlong (interface : Interface Process Name)
    (nameRel : Name -> Name -> Prop) : Prop :=
  forall name, nameRel (interface.quote (interface.drop name)) name

/-- Proof-relevant execution of a dropped quotation.  The witness type may
retain a route, occurrence, schedule, provenance, or cost receipt. -/
def OperationalBeta (interface : Interface Process Name)
    (Step : Process -> Process -> Type uStep) : Type (max uProcess uStep) :=
  forall process, Step (interface.drop (interface.quote process)) process

/-- An operational relation reflects literal equality when every one of its
witnesses forces its endpoints to be equal.  This is deliberately stronger
than soundness with respect to a coarser behavioral equivalence. -/
def StepReflectsEquality (Step : Process -> Process -> Type uStep) : Prop :=
  forall {source target}, Step source target -> source = target

/-- Static beta makes quotation injective. -/
theorem quote_injective_of_staticBeta (interface : Interface Process Name)
    (beta : interface.StaticBeta) : Function.Injective interface.quote := by
  intro left right sameQuote
  calc
    left = interface.drop (interface.quote left) := (beta left).symm
    _ = interface.drop (interface.quote right) := congrArg interface.drop sameQuote
    _ = right := beta right

/-- Static beta makes dropping surjective. -/
theorem drop_surjective_of_staticBeta (interface : Interface Process Name)
    (beta : interface.StaticBeta) : Function.Surjective interface.drop := by
  intro process
  exact ⟨interface.quote process, beta process⟩

/-- Static eta makes dropping injective. -/
theorem drop_injective_of_staticEta (interface : Interface Process Name)
    (eta : interface.StaticEta) : Function.Injective interface.drop := by
  intro left right sameDrop
  calc
    left = interface.quote (interface.drop left) := (eta left).symm
    _ = interface.quote (interface.drop right) := congrArg interface.quote sameDrop
    _ = right := eta right

/-- Static eta makes quotation surjective. -/
theorem quote_surjective_of_staticEta (interface : Interface Process Name)
    (eta : interface.StaticEta) : Function.Surjective interface.quote := by
  intro name
  exact ⟨interface.drop name, eta name⟩

/-- Literal beta and eta exhibit a genuine equivalence between processes and
names. -/
def exactEquiv (interface : Interface Process Name)
    (beta : interface.StaticBeta) (eta : interface.StaticEta) :
    Process ≃ Name where
  toFun := interface.quote
  invFun := interface.drop
  left_inv := beta
  right_inv := eta

/-- Literal beta makes dropping a split readout whose canonical
representatives are quotations. -/
def betaReadout (interface : Interface Process Name)
    (beta : interface.StaticBeta) : SplitReadout Name Process where
  observe := interface.drop
  representative := interface.quote
  observe_representative := beta

/-- Given beta, eta is exactly faithfulness of the drop readout. -/
theorem betaReadout_faithful_iff_eta (interface : Interface Process Name)
    (beta : interface.StaticBeta) :
    (interface.betaReadout beta).Faithful <-> interface.StaticEta := by
  simpa [betaReadout, StaticEta, SplitReadout.canonicalize] using
    SplitReadout.faithful_iff_canonicalize_eq
      (interface.betaReadout beta)

/-- A proof-relevant operational beta yields static beta only when the step
relation reflects literal endpoint equality. -/
theorem staticBeta_of_operationalBeta
    (interface : Interface Process Name)
    {Step : Process -> Process -> Type uStep}
    (execution : interface.OperationalBeta Step)
    (reflects : StepReflectsEquality Step) :
    interface.StaticBeta := by
  intro process
  exact reflects (execution process)

/-- Conversely, literal beta yields an operational beta for every reflexive
step discipline. -/
def operationalBeta_of_staticBeta
    (interface : Interface Process Name)
    {Step : Process -> Process -> Type uStep}
    (beta : interface.StaticBeta)
    (refl : forall process, Step process process) :
    interface.OperationalBeta Step := by
  intro process
  rw [beta process]
  exact refl process

/-! ## Exactness after selected quotients -/

/-- Quotation and dropping respect independently selected equivalence
relations.  This is the data needed to descend the interface to quotients. -/
structure QuotientCompatibility (interface : Interface Process Name)
    (processEq : Setoid Process) (nameEq : Setoid Name) where
  quote_respects : forall {left right}, processEq.r left right ->
    nameEq.r (interface.quote left) (interface.quote right)
  drop_respects : forall {left right}, nameEq.r left right ->
    processEq.r (interface.drop left) (interface.drop right)

namespace QuotientCompatibility

variable (interface : Interface Process Name)
variable {processEq : Setoid Process} {nameEq : Setoid Name}

/-- Quotation induced on quotient carriers. -/
def quotientQuote
    (compatibility : QuotientCompatibility interface processEq nameEq) :
    Quotient processEq -> Quotient nameEq :=
  Quotient.map interface.quote
    (fun _ _ related => compatibility.quote_respects related)

/-- Dropping induced on quotient carriers. -/
def quotientDrop
    (compatibility : QuotientCompatibility interface processEq nameEq) :
    Quotient nameEq -> Quotient processEq :=
  Quotient.map interface.drop
    (fun _ _ related => compatibility.drop_respects related)

/-- Relational process beta becomes literal beta after quotienting. -/
theorem quotient_beta
    (compatibility : QuotientCompatibility interface processEq nameEq)
    (beta : interface.BetaAlong processEq.r) :
    Function.LeftInverse compatibility.quotientDrop
      compatibility.quotientQuote := by
  intro processClass
  refine Quotient.inductionOn processClass ?_
  intro process
  apply Quotient.sound
  exact beta process

/-- Relational name eta becomes literal eta after quotienting. -/
theorem quotient_eta
    (compatibility : QuotientCompatibility interface processEq nameEq)
    (eta : interface.EtaAlong nameEq.r) :
    Function.RightInverse compatibility.quotientDrop
      compatibility.quotientQuote := by
  intro nameClass
  refine Quotient.inductionOn nameClass ?_
  intro name
  apply Quotient.sound
  exact eta name

/-- Relative beta and eta exhibit an equivalence of the selected quotient
carriers.  The theorem says nothing about raw-syntax equality. -/
def quotientEquiv
    (compatibility : QuotientCompatibility interface processEq nameEq)
    (beta : interface.BetaAlong processEq.r)
    (eta : interface.EtaAlong nameEq.r) :
    Quotient processEq ≃ Quotient nameEq where
  toFun := compatibility.quotientQuote
  invFun := compatibility.quotientDrop
  left_inv := quotient_beta interface compatibility beta
  right_inv := quotient_eta interface compatibility eta

end QuotientCompatibility

end Interface

/-! ## Independence canaries -/

namespace Canary

/-- A reflection interface with one name and two processes.  Eta holds, while
beta cannot hold as literal equality. -/
def etaOnly : Interface Bool PUnit where
  quote := fun _ => PUnit.unit
  drop := fun _ => false

theorem etaOnly_staticEta : etaOnly.StaticEta := by
  intro name
  cases name
  rfl

theorem etaOnly_not_staticBeta : ¬ etaOnly.StaticBeta := by
  intro beta
  have falseEqualsTrue := beta true
  exact Bool.false_ne_true falseEqualsTrue

theorem etaOnly_quote_not_injective : ¬ Function.Injective etaOnly.quote := by
  intro injective
  exact Bool.false_ne_true (injective rfl)

/-- A maximally permissive proof-relevant step relation. -/
def UniversalStep (_source _target : Bool) : Type := PUnit

/-- Operational execution can exist even when quotation is not injective and
literal beta is false. -/
def etaOnly_operationalBeta : etaOnly.OperationalBeta UniversalStep :=
  fun _ => PUnit.unit

theorem operationalBeta_and_eta_do_not_imply_staticBeta :
    Nonempty (etaOnly.OperationalBeta UniversalStep) /\
      etaOnly.StaticEta /\
      ¬ etaOnly.StaticBeta :=
  ⟨⟨etaOnly_operationalBeta⟩, etaOnly_staticEta, etaOnly_not_staticBeta⟩

/-- The permissive operational relation does not reflect equality. -/
theorem universalStep_not_reflectsEquality :
    ¬ Interface.StepReflectsEquality UniversalStep := by
  intro reflects
  exact Bool.false_ne_true (reflects (source := false) (target := true) PUnit.unit)

/-- A proof-relevant step may retain two distinct receipts for the same
execution endpoints. -/
def TwoReceiptStep (_source _target : Bool) : Type := Bool

def twoReceiptOperationalBeta : etaOnly.OperationalBeta TwoReceiptStep :=
  fun _ => false

theorem two_receipts_same_endpoints :
    (false : TwoReceiptStep false false) ≠ true :=
  Bool.false_ne_true

/-- The identity interface supplies the fully exact positive control. -/
def exactBool : Interface Bool Bool where
  quote := id
  drop := id

theorem exactBool_beta : exactBool.StaticBeta := fun _ => rfl
theorem exactBool_eta : exactBool.StaticEta := fun _ => rfl

theorem exactBool_equivalence : Function.Bijective exactBool.quote :=
  (exactBool.exactEquiv exactBool_beta exactBool_eta).bijective

end Canary

#print axioms Interface.quote_injective_of_staticBeta
#print axioms Interface.drop_surjective_of_staticBeta
#print axioms Interface.drop_injective_of_staticEta
#print axioms Interface.quote_surjective_of_staticEta
#print axioms Interface.exactEquiv
#print axioms Interface.betaReadout_faithful_iff_eta
#print axioms Interface.staticBeta_of_operationalBeta
#print axioms Interface.QuotientCompatibility.quotientEquiv
#print axioms Canary.etaOnly_not_staticBeta
#print axioms Canary.operationalBeta_and_eta_do_not_imply_staticBeta
#print axioms Canary.universalStep_not_reflectsEquality
#print axioms Canary.two_receipts_same_endpoints

end Mettapedia.Computability.ReflectiveCode
