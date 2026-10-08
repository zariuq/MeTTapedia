import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinementModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPropositions
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementInterpretationControls

/-!
# Distinct generated refinement values with the same logical guard

The ordinary proposition values quoting truth and falsehood remain distinct
in the actual generated term quotient. The distinction follows from the
independent varying native model and the generated soundness theorem. Both
values satisfy the same refinement guard; recording only that guard would
erase their distinction. A supplied context extension also exercises the
complete refinement introduction and forgetting substitution equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementControls

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open RefinementValues QuotientComprehensionSyntax
open DisplayedPresheafTransport DisplayedPresheafComprehension
open Mettapedia.GSLT.Core.ContextualLadder.TypeOver (extensionSubstitution)

abbrev context : Context Controls.signature := Contextual.empty Controls.signature
abbrev qcontext : QuotientCwf.QContext Controls.signature :=
  (quotientProjection Controls.signature).obj context

def domain : QuotientCwf.Ty qcontext := QType.mk (propositionsType context)
def truthTerm : Term context (propositionsType context) := quotePredicate (Logic.truth context)
def falseTerm : Term context (propositionsType context) := quotePredicate (Logic.falsehood context)

def truthValue : QuotientCwf.Tm qcontext domain := ⟨QTerm.mk truthTerm, rfl⟩
def falseValue : QuotientCwf.Tm qcontext domain := ⟨QTerm.mk falseTerm, rfl⟩

theorem predicates_remain_distinct :
    QPredicate.mk (Logic.truth context) ≠ QPredicate.mk (Logic.falsehood context) := by
  intro equality
  rcases (QPredicate.mk_eq_iff _ _).mp equality with ⟨tree⟩
  have sound := tree.native_sound InterpretationControls.model InterpretationControls.realization
  have falseRead := Interprets.predicateEqAt sound InterpretationControls.emptyScope ⊤ rfl rfl
  have impossible : (⊥ : Subfunctor InterpretationControls.emptyScope.1) = ⊤ :=
    Option.some.inj falseRead
  have belongs : PUnit.unit ∈
      (⊥ : Subfunctor InterpretationControls.emptyScope.1).obj
        (Opposite.op WalkingParallelPair.zero) := by
    rw [impossible]
    trivial
  exact belongs

theorem supplied_classes_remain_distinct : truthValue.val ≠ falseValue.val := by
  intro equality
  have equation := ((QTerm.mk_eq_iff truthTerm falseTerm).mp equality).2
  have propositionClasses : QPropositionTerm.mk truthTerm = QPropositionTerm.mk falseTerm :=
    _root_.Quotient.sound equation
  have predicates := congrArg QPropositionTerm.holds propositionClasses
  change (QPredicate.mk (Logic.truth context)).quote.holds =
    (QPredicate.mk (Logic.falsehood context)).quote.holds at predicates
  rw [QPredicate.holds_quote, QPredicate.holds_quote] at predicates
  exact predicates_remain_distinct predicates

noncomputable def selected : QPredicate (QuotientCwf.ext qcontext domain).as := ⊤

theorem supplied_guard (value : QuotientCwf.Tm qcontext domain) :
    (guard selected value).entails := by
  change (predicateSub (⊤ : QPredicate (QuotientCwf.ext qcontext domain).as) _).entails
  rw [predicateSub_representative, Logic.top_reindex]
  exact (Logic.entails_iff_eq_top _).mpr rfl

noncomputable def refinedTruth := intro selected truthValue (supplied_guard truthValue)
noncomputable def refinedFalse := intro selected falseValue (supplied_guard falseValue)

theorem source_beta_retains_truth : forget selected refinedTruth = truthValue :=
  beta _ _ _

theorem source_beta_retains_falsehood : forget selected refinedFalse = falseValue :=
  beta _ _ _

theorem selected_values_remain_distinct : refinedTruth ≠ refinedFalse := by
  intro equality
  have underlying := congrArg (forget selected) equality
  rw [source_beta_retains_truth, source_beta_retains_falsehood] at underlying
  exact supplied_classes_remain_distinct (congrArg Subtype.val underlying)

/-- Keeping only the logical guard identifies values that remain
distinct in the actual generated refinement term fibre. -/
theorem logical_guard_alone_erases_the_supplied_value :
    guard selected (forget selected refinedTruth) =
        guard selected (forget selected refinedFalse) ∧ refinedTruth ≠ refinedFalse := by
  constructor
  · rw [guard_forget_top, guard_forget_top]
  · exact selected_values_remain_distinct

abbrev extended : Context Controls.signature := extend context (propositionsType context)
abbrev qextended : QuotientCwf.QContext Controls.signature :=
  (quotientProjection Controls.signature).obj extended

def dropVariable : qextended ⟶ qcontext :=
  QuotientCwf.project (projectionHom context (propositionsType context))

theorem extension_changes_raw_scope : extended.arity ≠ context.arity := by decide

noncomputable def transportedTruth := QuotientCwf.tmSub refinedTruth dropVariable
noncomputable def pulledPredicate :=
  predicateSub selected (extensionSubstitution (C := QuotientCwf.cwf Controls.signature) dropVariable domain)

theorem transported_guard :
    (guard pulledPredicate (QuotientCwf.tmSub truthValue dropVariable)).entails :=
  guard_entails_substitution dropVariable selected truthValue (supplied_guard truthValue)

noncomputable def independentTruth := intro pulledPredicate
  (QuotientCwf.tmSub truthValue dropVariable) transported_guard

theorem complete_introduction_substitution : HEq transportedTruth independentTruth :=
  intro_substitution dropVariable selected truthValue (supplied_guard truthValue) transported_guard

theorem complete_forgetting_substitution :
    HEq (QuotientCwf.tmSub (forget selected refinedTruth) dropVariable)
      (forget pulledPredicate independentTruth) :=
  forget_substitution dropVariable selected refinedTruth independentTruth complete_introduction_substitution

theorem independently_formed_type_substitution :
    QuotientCwf.tySub (Refinements.type domain selected) dropVariable =
      Refinements.type (QuotientCwf.tySub domain dropVariable) pulledPredicate :=
  formation_substitution dropVariable domain selected

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementControls
