import Mettapedia.OSLF.Syntax.ScopedOperationalEvidenceExponential
import Mettapedia.OSLF.Syntax.SemanticScopedPremiseInterpretation

/-!
# Authored premise evidence in contextual function form

A scoped step premise asks for individual evidence at an interpreted judgment
under its declared local binders. The comparison here identifies that fiber
with contextual functions whose read-back has exactly that judgment. The
endpoint condition is separate from the function-space construction, and
different evidence values at the same endpoints remain different functions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedPremiseEvidenceComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BinderLocalPremise

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- Recover the full sorted judgment indexed by one retained event. -/
def eventJudgment
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y : SubstitutionModel R A} {Γ : Ctx S}
    (event : ModelEvent R Y Γ) :
    Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A :=
  ⟨Γ, event.1, event.2.1⟩

/-- The ordinary evidence fiber is exactly the fiber of the retained event
object over its sorted endpoints. No event is identified with another. -/
def eventFiberEquiv
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    (j : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) :
    Y.evidence.carrier () j ≃
      {event : ModelEvent R Y j.1 // eventJudgment R event = j} := by
  rcases j with ⟨Γ, sort, pair⟩
  refine {
    toFun := fun evidence => ⟨⟨sort, pair, evidence⟩, rfl⟩
    invFun := fun event => event.2 ▸ event.1.2.2
    left_inv := ?_
    right_inv := ?_ }
  · intro evidence
    rfl
  · rintro ⟨⟨eventSort, eventPair, evidence⟩, same⟩
    have inner :
        (⟨eventSort, eventPair⟩ :
          Σ sort : S.Srt,
            A.substitution.Carrier Γ sort ×
              A.substitution.Carrier Γ sort) =
        ⟨sort, pair⟩ :=
      eq_of_heq (Sigma.mk.inj_iff.mp same).2
    have sortEq : eventSort = sort := (Sigma.mk.inj_iff.mp inner).1
    cases sortEq
    have pairEq : eventPair = pair :=
      eq_of_heq (Sigma.mk.inj_iff.mp inner).2
    cases pairEq
    rfl

/-- Reading a contextual function at the generic binder variables gives
the event's full judgment, including the individual evidence witness. -/
noncomputable def scopedEventJudgment
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    (Γ scope : Ctx S)
    (function : ((MultiBinderPresheaf.binders A scope).functorHom
        (modelEvents R Y)).obj
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ))) :
    Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A :=
  eventJudgment R
    (modelScopedEventEquiv R A Y
      (ContextObject.ofList A.substitution.toClone Γ) scope function)

/-- Every authored premise has an exact contextual evidence fiber. The
condition on a function is its interpreted premise judgment, not merely
existence of some reduction between unspecified endpoints. -/
noncomputable def premiseEvidenceEquiv
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    {Ξ Γ : Ctx S} (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ) :
    Y.evidence.carrier () (interpretPremise A valuation close premise) ≃
      {function : ((MultiBinderPresheaf.binders A premise.binders).functorHom
          (modelEvents R Y)).obj
            (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) //
        scopedEventJudgment R Y Γ premise.binders function =
          interpretPremise A valuation close premise} := by
  let j := interpretPremise A valuation close premise
  let compare := modelScopedEventEquiv R A Y
    (ContextObject.ofList A.substitution.toClone Γ) premise.binders
  let fiber := eventFiberEquiv R Y j
  change Y.evidence.carrier () j ≃
    {function : ((MultiBinderPresheaf.binders A premise.binders).functorHom
        (modelEvents R Y)).obj
          (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) //
      eventJudgment R (compare function) = j}
  exact fiber.trans (Equiv.subtypeEquivOfSubtype compare).symm

/-- The contextual function associated with a premise witness is obtained
by currying that very witness at its authored source and target. -/
theorem premiseEvidenceEquiv_function
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    {Ξ Γ : Ctx S} (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ)
    (evidence : Y.evidence.carrier ()
      (interpretPremise A valuation close premise)) :
    (premiseEvidenceEquiv R Y valuation close premise evidence).1 =
      (modelScopedEventEquiv R A Y
        (ContextObject.ofList A.substitution.toClone Γ)
        premise.binders).symm
        ⟨premise.sort,
          ((interpretPremise A valuation close premise).2.2.1,
            (interpretPremise A valuation close premise).2.2.2),
          evidence⟩ := by
  rfl

/-- An interpretation of individual rule evidence commutes with currying
every authored scoped premise. This is the map law required for the
operational classifier to act on interpretation morphisms. -/
theorem premiseEvidenceEquiv_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    {Ξ Γ : Ctx S} (valuation : Valuation (M := M) A Γ)
    (close : Environment S A.substitution.Carrier Ξ Γ)
    (premise : LocalStepPremise (withMetas S M) Ξ)
    (evidence : Y.evidence.carrier ()
      (interpretPremise A valuation close premise)) :
    (premiseEvidenceEquiv R Z valuation close premise
      (h.evidence.toFun ()
        (interpretPremise A valuation close premise) evidence)).1 =
      (((FunctorToTypes.rightAdj
        (MultiBinderPresheaf.binders A premise.binders)).map
          (mapModelEvents R h)).app
            (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)))
        (premiseEvidenceEquiv R Y valuation close premise evidence).1 := by
  let context := ContextObject.ofList A.substitution.toClone Γ
  let compareZ := modelScopedEventEquiv R A Z context premise.binders
  let compareY := modelScopedEventEquiv R A Y context premise.binders
  let sourceEvent : ModelEvent R Y (premise.binders ++ Γ) :=
    ⟨premise.sort,
      ((interpretPremise A valuation close premise).2.2.1,
        (interpretPremise A valuation close premise).2.2.2), evidence⟩
  let targetEvent : ModelEvent R Z (premise.binders ++ Γ) :=
    ⟨premise.sort,
      ((interpretPremise A valuation close premise).2.2.1,
        (interpretPremise A valuation close premise).2.2.2),
      h.evidence.toFun ()
        (interpretPremise A valuation close premise) evidence⟩
  apply compareZ.injective
  rw [modelScopedEvent_map]
  rw [premiseEvidenceEquiv_function, premiseEvidenceEquiv_function]
  change compareZ (compareZ.symm targetEvent) =
    (mapModelEvents R h).app
      (Opposite.op (ContextObject.ofList A.substitution.toClone
        (premise.binders ++ Γ)))
      (compareY (compareY.symm sourceEvent))
  have leftRead : compareZ (compareZ.symm targetEvent) = targetEvent :=
    compareZ.apply_symm_apply targetEvent
  have rightRead : compareY (compareY.symm sourceEvent) = sourceEvent :=
    compareY.apply_symm_apply sourceEvent
  rw [leftRead, rightRead]
  rfl

/-- The contextual-function input type of one actual rule occurrence. Each
ordered premise position retains its own binder list, endpoint sort, and
evidence judgment. Equal endpoint pairs at two positions do not merge them. -/
abbrev ScopedRuleInputs
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    (occurrence : Instance R A) : Type u :=
  ∀ position : Fin (R.get occurrence.index).premises.length,
    let premise := (R.get occurrence.index).premises.get position
    {function : ((MultiBinderPresheaf.binders A premise.binders).functorHom
        (modelEvents R Y)).obj
          (Opposite.op (ContextObject.ofList A.substitution.toClone
            occurrence.ambient)) //
      scopedEventJudgment R Y occurrence.ambient premise.binders function =
        childJudgment R A occurrence position}

/-- The complete ordered child input of the operational rule polynomial is
equivalent to the complete family of contextual premise functions. This is
the interaction between the authored polynomial and categorical binding. -/
noncomputable def ruleInputsEquiv
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    (occurrence : Instance R A) :
    (∀ position : Fin (R.get occurrence.index).premises.length,
      Y.evidence.carrier () (childJudgment R A occurrence position)) ≃
      ScopedRuleInputs R Y occurrence :=
  Equiv.piCongrRight fun position =>
    premiseEvidenceEquiv R Y occurrence.valuation occurrence.close
      ((R.get occurrence.index).premises.get position)

/-- Interpreting a rule constructor after reading each contextual premise
function is the original proof-relevant rule action. Its output keeps the
constructor occurrence and exact ordered child evidence. -/
noncomputable def scopedRuleAction
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    (occurrence : Instance R A)
    (inputs : ScopedRuleInputs R Y occurrence) :
    Y.evidence.carrier () (conclusionJudgment R A occurrence) :=
  Y.evidence.rules.act () (conclusionJudgment R A occurrence)
    ⟨⟨occurrence, rfl⟩, (ruleInputsEquiv R Y occurrence).symm inputs⟩

/-- The contextual presentation neither invents nor discards a premise
firing: converting all children to functions and applying the rule agrees
with applying the model's authored constructor to those very children. -/
theorem scopedRuleAction_ofChildren
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Y.evidence.carrier () (childJudgment R A occurrence position)) :
    scopedRuleAction R Y occurrence
      (ruleInputsEquiv R Y occurrence children) =
        Y.evidence.rules.act () (conclusionJudgment R A occurrence)
          ⟨⟨occurrence, rfl⟩, children⟩ := by
  unfold scopedRuleAction
  rw [(ruleInputsEquiv R Y occurrence).symm_apply_apply]

/-- A map of lawful operational models preserves the scoped rule action,
including each individually mapped premise firing at its original position. -/
theorem scopedRuleAction_map
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z)
    (occurrence : Instance R A)
    (children : ∀ position : Fin (R.get occurrence.index).premises.length,
      Y.evidence.carrier () (childJudgment R A occurrence position)) :
    h.evidence.toFun () (conclusionJudgment R A occurrence)
      (scopedRuleAction R Y occurrence
        (ruleInputsEquiv R Y occurrence children)) =
      scopedRuleAction R Z occurrence
        (ruleInputsEquiv R Z occurrence
          (fun position => h.evidence.toFun ()
            (childJudgment R A occurrence position) (children position))) := by
  rw [scopedRuleAction_ofChildren, scopedRuleAction_ofChildren]
  exact h.evidence.commutes () (conclusionJudgment R A occurrence)
    ⟨⟨occurrence, rfl⟩, children⟩

#print axioms eventFiberEquiv
#print axioms premiseEvidenceEquiv
#print axioms premiseEvidenceEquiv_map
#print axioms ruleInputsEquiv
#print axioms scopedRuleAction_ofChildren
#print axioms scopedRuleAction_map

end Mettapedia.OSLF.Binding.ScopedPremiseEvidenceComparison
