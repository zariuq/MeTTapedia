import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction

/-!
# The selected interaction rules of the existing instances are base rules

The definition of an interactive GSLT asks for a base rewrite headed by the
contact constructor.  `InteractivePresentation` records the heading and
leaves the absence of reduction hypotheses to be checked.  It holds for each
presentation already in the tree: communication in rho and beta in lambda
have no premise at all, and communication in the MeTTa-calculus has a single
relation query, which is a side condition and not a reduction of a subterm.

Rho's contextual rule is the control: it has a reduction hypothesis, it is
headed by the same contact, and it is not a base rule.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction

/-- Rho's communication rule is a base rule. -/
theorem rho_baseInteraction : rhoInteractivePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- Beta is a base rule. -/
theorem lambda_baseInteraction : lambdaInteractivePresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- The MeTTa-calculus communication rule is a base rule: its one premise is
a relation query. -/
theorem mettaCalc_baseInteraction :
    mettaCalcInteractivePresentation.BaseInteraction := by
  decide

/-- Rho is interactive. -/
theorem rhoCalc_isInteractive : IsInteractive rhoCalc :=
  rhoInteractivePresentation.isInteractive rho_baseInteraction

/-- The lambda calculus is interactive. -/
theorem lambdaCalc_isInteractive :
    IsInteractive lambdaInteractivePresentation.presentation.language :=
  lambdaInteractivePresentation.isInteractive lambda_baseInteraction

/-- The MeTTa-calculus is interactive. -/
theorem mettaCalc_isInteractive :
    IsInteractive mettaCalcInteractivePresentation.presentation.language :=
  mettaCalcInteractivePresentation.isInteractive mettaCalc_baseInteraction

/-- The MeTTa-calculus communication rule carries a premise: its contractum
is computed by a relation query and is not a schema over what the redex
matched.  No iGSLT over this presentation has an interaction-cut
presentation. -/
theorem mettaCalc_no_interactionCut (theory : IGSLT)
    (same : theory.presentation = mettaCalcInteractivePresentation) :
    IsEmpty (InteractionCutPresentation theory) := by
  constructor
  intro cut
  have premiseFree := cut.interactionPremisesEmpty
  rw [same] at premiseFree
  exact absurd premiseFree (by decide)

/-- Rho's contextual rule asks for a reduction of a component: it is not a
base rule. -/
theorem rho_parCong_not_base : ¬ IsBaseRewrite rhoParCongRewrite :=
  not_isBaseRewrite_of_congruence (source := .fvar "S") (target := .fvar "T")
    (List.Mem.head _)

end Mettapedia.GSLT.LanguageDef
