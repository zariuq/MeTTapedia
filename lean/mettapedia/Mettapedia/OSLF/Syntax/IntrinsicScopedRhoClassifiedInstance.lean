import Mettapedia.OSLF.Syntax.RhoPayloadPresentation
import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedReduction

/-!
# The actual rho payload presentation in the general classification

The strict and book profiles retain the authored payload continuation,
COMM and ParCong declarations, and contextual parallel and quote/drop
equations. Events are existing complete trees over equation-class states;
no raw event quotient or silent telescope pruning is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedRhoClassifiedInstance

open RhoPayloadPresentation
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedSharedLocalPolynomialComparison (localRules)
open IntrinsicScopedSharedLocalTreeComparison (toLocalTree toSharedTree)
open IntrinsicScopedAuthoredClassifiedInstance (algebra)
open IntrinsicScopedAuthoredClassifiedReduction (ExtendedReduction)

abbrev strictLocalRules := localRules strictRules
abbrev bookLocalRules := localRules bookRules

abbrev strictModel := IntrinsicScopedAuthoredClassifiedInstance.model strictLocalRules equations
abbrev bookModel := IntrinsicScopedAuthoredClassifiedInstance.model bookLocalRules equations
abbrev strictClassified := IntrinsicScopedAuthoredClassifiedInstance.classified strictLocalRules equations
abbrev bookClassified := IntrinsicScopedAuthoredClassifiedInstance.classified bookLocalRules equations
abbrev strictInterpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation strictLocalRules equations
abbrev bookInterpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation bookLocalRules equations
abbrev strictRestrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso strictLocalRules equations
abbrev bookRestrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso bookLocalRules equations
abbrev strictRecoveredModelIso := IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso strictLocalRules equations
abbrev bookRecoveredModelIso := IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso bookLocalRules equations

/-- Both original profiles retain the complete payload continuation telescope. -/
theorem strict_rule_inventory : strictLocalRules = [⟨metas, comm⟩, ⟨metas, parCong⟩] := rfl
theorem book_rule_inventory : bookLocalRules = [⟨metas, comm⟩, ⟨metas, parCong⟩, ⟨metas, drop⟩] := rfl

/-- The original ordered child of parallel congruence is retained. -/
theorem ordered_premise_binders :
    bookLocalRules.map (fun declaration => declaration.2.premises.map (fun premise => premise.binders)) =
      [[], [[]], []] := rfl

/-- All four actual authored equations are part of this same classified presentation. -/
theorem equation_inventory : equations = [commPar, assocPar, unitPar, quoteDrop] := rfl

/-- The existing whole-history adapter is exact for every actual class-state step. -/
theorem steps_iff_tree (R : List (IntrinsicScopedConditionalPolynomial.Rule sig metas))
    {Γ : Ctx sig} (source target : Term sig Γ Srt.pr) :
    Steps R source target ↔
      Nonempty (IntrinsicScopedLocalPolynomial.Tree (localRules R) (algebra equations)
        (mapJudgment classes
          (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)))) := by
  constructor
  · rintro ⟨tree⟩
    exact ⟨toLocalTree R _ _ tree⟩
  · rintro ⟨tree⟩
    exact ⟨toSharedTree R _ _ tree⟩

/-- The genuine extended generic reduction covers precisely the existing
payload presentation's steps, including its equation-class endpoints. -/
theorem extension_iff_steps (R : List (IntrinsicScopedConditionalPolynomial.Rule sig metas))
    {Γ : Ctx sig} (source target : Term sig Γ Srt.pr) :
    ExtendedReduction (localRules R) equations source target ↔ Steps R source target :=
  (IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree (localRules R) equations
    source target).trans (steps_iff_tree R source target).symm

/-- COMM is classified for every typed channel, payload, continuation and ordinary context. -/
theorem comm_classified (rest : List (IntrinsicScopedConditionalPolynomial.Rule sig metas))
    {Γ : Ctx sig} (channel : Term sig Γ Srt.nm) (payload : Term sig Γ Srt.pr)
    (K : Term sig (Srt.pr :: Γ) Srt.pr) :
    ExtendedReduction (localRules (comm :: parCong :: rest)) equations
      (parT (outT channel payload) (inpT channel K)) (inst K payload) :=
  (extension_iff_steps _ _ _).mpr (steps_comm rest channel payload K)

/-- The ordered ParCong child is an actual interpreted reduction section. -/
theorem parCong_classified (rest : List (IntrinsicScopedConditionalPolynomial.Rule sig metas))
    {Γ : Ctx sig} {source target : Term sig Γ Srt.pr} (other : Term sig Γ Srt.pr)
    (child : ExtendedReduction (localRules (comm :: parCong :: rest)) equations source target) :
    ExtendedReduction (localRules (comm :: parCong :: rest)) equations
      (parT source other) (parT target other) :=
  (extension_iff_steps _ _ _).mpr
    (steps_parCong rest other ((extension_iff_steps _ _ _).mp child))

/-- The book Drop firing is present in the actual interpreted profile. -/
theorem drop_book_classified {Γ : Ctx sig} (code : Term sig Γ Srt.pr) :
    ExtendedReduction bookLocalRules equations (drpT (quoT code)) code :=
  (extension_iff_steps _ _ _).mpr (drop_runs_book code)

/-- The same redex has no strict-profile interpreted reduction, to any target class. -/
theorem drop_strict_not_classified {Γ : Ctx sig} (code target : Term sig Γ Srt.pr) :
    ¬ ExtendedReduction strictLocalRules equations (drpT (quoT code)) target := by
  intro firing
  exact drop_inert_strict code target ((extension_iff_steps _ _ _).mp firing)

end Mettapedia.OSLF.Binding.IntrinsicScopedRhoClassifiedInstance
