import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredOperationalProfile
import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedReduction

/-!
# The actual name-passing runtime in its equation-classified operational model

The independent two scope schemas supply the equation quotient, and the
independent five-rule active profile supplies proof-relevant firing trees.
Arbitrary quotient-valued rule assignments are lifted at their exact binder
contexts. The resulting generic reduction agrees with the independently
supplied beta/fetch occurrences modulo the two static scope laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredClassified

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial (Instance Tree)
open Presentation AuthoredEquations AuthoredOperationalProfile

abbrev algebra := BindingEquationQuotientModel.algebra equations
abbrev projection := BindingEquationQuotientModel.projection equations
abbrev model := IntrinsicScopedAuthoredClassifiedInstance.model rules equations
abbrev classified := IntrinsicScopedAuthoredClassifiedInstance.classified rules equations
abbrev interpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation rules equations
abbrev restrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso rules equations
abbrev recoveredModelIso := IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso rules equations

/-- Static equality surrounds an actual supplied active-edge occurrence. -/
def StepModulo {Γ : Ctx signature} (first last : Program Γ) : Prop :=
  ∃ redex reduct : Program Γ,
    StaticEq first redex ∧ Nonempty (ActiveEdge redex reduct) ∧ StaticEq reduct last

theorem active_toModulo {Γ : Ctx signature} {first last : Program Γ}
    (edge : ActiveEdge first last) : StepModulo first last :=
  ⟨first, last, .refl _, ⟨edge⟩, .refl _⟩

/-- Select a representative separately for every value at its actual local
context. The rule index and ambient context do not change. -/
def liftOccurrence (occurrence : Instance rules algebra) :
    Instance rules (BindingCloneAlgebra.terms signature) where
  index := occurrence.index
  ambient := occurrence.ambient
  valuation := fun index => Quotient.out (occurrence.valuation index)
  close := fun sort name => Quotient.out (occurrence.close sort name)

theorem map_liftOccurrence (occurrence : Instance rules algebra) :
    IntrinsicScopedLocalPolynomial.mapInstance rules projection (liftOccurrence occurrence) =
      occurrence := by
  cases occurrence
  dsimp only [IntrinsicScopedLocalPolynomial.mapInstance, liftOccurrence,
    SemanticContextualMetavariables.mapValuation, projection,
    BindingEquationQuotientModel.projection]
  congr 1
  · funext index
    exact Quotient.out_eq _
  · funext sort name
    exact Quotient.out_eq _

theorem stepModulo_application {Γ : Ctx signature} {first last : Program Γ}
    (argument : Name Γ) (step : StepModulo first last) :
    StepModulo (Presentation.application first argument) (Presentation.application last argument) := by
  obtain ⟨redex, reduct, before, ⟨edge⟩, after⟩ := step
  exact ⟨Presentation.application redex argument, Presentation.application reduct argument,
    .application argument before, ⟨.application argument edge⟩, .application argument after⟩

theorem stepModulo_definition {Γ : Ctx signature} {first last : Program (.nm :: Γ)}
    (value : Program Γ) (step : StepModulo first last) :
    StepModulo (Presentation.definition value first) (Presentation.definition value last) := by
  obtain ⟨redex, reduct, before, ⟨edge⟩, after⟩ := step
  exact ⟨Presentation.definition value redex, Presentation.definition value reduct,
    .definition (.refl value) before, ⟨.definition value edge⟩, .definition (.refl value) after⟩

theorem stepModulo_carrier {Γ : Ctx signature} {first last : Program Γ}
    (name : Name Γ) (value : Program Γ) (step : StepModulo first last) :
    StepModulo (Presentation.carrier name value first) (Presentation.carrier name value last) := by
  obtain ⟨redex, reduct, before, ⟨edge⟩, after⟩ := step
  exact ⟨Presentation.carrier name value redex, Presentation.carrier name value reduct,
    .carrier name (.refl value) before, ⟨.carrier name value edge⟩, .carrier name (.refl value) after⟩

def sourceStepModulo : Judgment raw → Prop
  | ⟨_, .nm, _, _⟩ => False
  | ⟨_, .tm, first, last⟩ => StepModulo first last

/-- The actual static-saturated relation validates all independent active rules. -/
theorem sourceStepModulo_ruleClosed (occurrence : Instance rules raw)
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      sourceStepModulo (IntrinsicScopedLocalPolynomial.childJudgment rules raw occurrence position)) :
    sourceStepModulo (IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw occurrence) := by
  rcases occurrence with ⟨⟨index, bounded⟩, Γ, valuation, close⟩
  have small : index < 5 := by simpa [AuthoredOperationalProfile.rules] using bounded
  interval_cases index
  · have direct := sourceStep_ruleClosed
      (⟨⟨0, bounded⟩, Γ, valuation, close⟩ : Instance rules raw)
      (by intro position; nomatch position)
    rw [IntrinsicScopedLocalRawReadout.conclusion] at direct ⊢
    change Nonempty (ActiveEdge _ _) at direct
    obtain ⟨edge⟩ := direct
    exact active_toModulo edge
  · have direct := sourceStep_ruleClosed
      (⟨⟨1, bounded⟩, Γ, valuation, close⟩ : Instance rules raw)
      (by intro position; nomatch position)
    rw [IntrinsicScopedLocalRawReadout.conclusion] at direct ⊢
    change Nonempty (ActiveEdge _ _) at direct
    obtain ⟨edge⟩ := direct
    exact active_toModulo edge
  · have child := children ⟨0, by simp [AuthoredOperationalProfile.rules, AuthoredOperationalProfile.application]⟩
    rw [IntrinsicScopedLocalRawReadout.child] at child
    change StepModulo (close .tm .zero) (close .tm (.succ .zero)) at child
    rw [IntrinsicScopedLocalRawReadout.conclusion]
    change StepModulo
      (Presentation.application (close .tm .zero) (close .nm (.succ (.succ .zero))))
      (Presentation.application (close .tm (.succ .zero)) (close .nm (.succ (.succ .zero))))
    exact stepModulo_application _ child
  · rw [definition_normalization valuation close bounded] at children ⊢
    have child := children ⟨0, by simp [AuthoredOperationalProfile.rules, definitionOccurrence, AuthoredOperationalProfile.definition]⟩
    rw [definition_child] at child
    rw [definition_conclusion]
    exact stepModulo_definition _ child
  · have child := children ⟨0, by simp [AuthoredOperationalProfile.rules, AuthoredOperationalProfile.carrier]⟩
    rw [IntrinsicScopedLocalRawReadout.child] at child
    change StepModulo (close .tm (.succ (.succ .zero)))
      (close .tm (.succ (.succ (.succ .zero)))) at child
    rw [IntrinsicScopedLocalRawReadout.conclusion]
    change StepModulo
      (Presentation.carrier (close .nm .zero) (close .tm (.succ .zero)) (close .tm (.succ (.succ .zero))))
      (Presentation.carrier (close .nm .zero) (close .tm (.succ .zero))
        (close .tm (.succ (.succ (.succ .zero)))))
    exact stepModulo_carrier _ _ child

/-- Replace both supplied endpoints by structurally equal representatives. -/
theorem stepModulo_of_equivalent {Γ : Ctx signature}
    {source source' target target' : Program Γ}
    (before : StaticEq source source') (after : StaticEq target' target)
    (step : StepModulo source' target') : StepModulo source target := by
  obtain ⟨redex, reduct, start, firing, finish⟩ := step
  exact ⟨redex, reduct, .trans before start, firing, .trans finish after⟩

/-- Runtime reduction on quotient judgments, read using arbitrary quotient
representatives. The following lemma proves that those choices do not affect
the supplied raw endpoints. -/
def quotientStep : Judgment algebra → Prop
  | ⟨_, .nm, _, _⟩ => False
  | ⟨_, .tm, source, target⟩ => StepModulo (Quotient.out source) (Quotient.out target)

theorem quotientStep_mapped_iff (judgment : Judgment (BindingCloneAlgebra.terms signature)) :
    quotientStep (mapJudgment projection judgment) ↔ sourceStepModulo judgment := by
  rcases judgment with ⟨Γ, sort, source, target⟩
  cases sort with
  | nm => rfl
  | tm =>
      have sourceEqual : StaticEq
          (Quotient.out (Quotient.mk _ source : TermQ equations Γ Srt.tm)) source :=
        AuthoredEquations.eqClosure_sound (show EqClosure equations
          (Quotient.out (Quotient.mk _ source : TermQ equations Γ Srt.tm)) source from
          Quotient.exact (Quotient.out_eq (Quotient.mk _ source : TermQ equations Γ Srt.tm)))
      have targetEqual : StaticEq
          (Quotient.out (Quotient.mk _ target : TermQ equations Γ Srt.tm)) target :=
        AuthoredEquations.eqClosure_sound (show EqClosure equations
          (Quotient.out (Quotient.mk _ target : TermQ equations Γ Srt.tm)) target from
          Quotient.exact (Quotient.out_eq (Quotient.mk _ target : TermQ equations Γ Srt.tm)))
      constructor
      · exact stepModulo_of_equivalent (.symm sourceEqual) targetEqual
      · exact stepModulo_of_equivalent sourceEqual (.symm targetEqual)

/-- Every quotient occurrence is checked through a raw representative of
that exact occurrence. Its child judgments are lifted at their own binder
contexts; their endpoint equalities are not replaced by another outcome. -/
theorem quotientStep_ruleClosed (occurrence : Instance rules algebra)
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      quotientStep (IntrinsicScopedLocalPolynomial.childJudgment rules algebra occurrence position)) :
    quotientStep (IntrinsicScopedLocalPolynomial.conclusionJudgment rules algebra occurrence) := by
  let lifted := liftOccurrence occurrence
  have rawChildren : ∀ position : Fin (rules.get lifted.index).2.premises.length,
      sourceStepModulo (IntrinsicScopedLocalPolynomial.childJudgment rules
        (BindingCloneAlgebra.terms signature) lifted position) := by
    intro position
    have compared : IntrinsicScopedLocalPolynomial.childJudgment rules algebra occurrence position =
        mapJudgment projection (IntrinsicScopedLocalPolynomial.childJudgment rules
          (BindingCloneAlgebra.terms signature) lifted position) := by
      have compared := IntrinsicScopedLocalPolynomial.mapInstance_child rules projection lifted position
      rcases occurrence with ⟨index, ambient, valuation, close⟩
      have values : SemanticContextualMetavariables.mapValuation projection
          (fun i => Quotient.out (valuation i)) = valuation := by
        funext i
        exact Quotient.out_eq _
      have names : (fun s x => projection.raw.map (Quotient.out (close s x))) = close := by
        funext s x
        exact Quotient.out_eq _
      dsimp only [lifted, liftOccurrence, IntrinsicScopedLocalPolynomial.mapInstance,
        ] at compared
      erw [values, names] at compared
      exact compared
    have child := children position
    rw [compared] at child
    exact (quotientStep_mapped_iff _).mp child
  have raw := sourceStepModulo_ruleClosed lifted rawChildren
  have result := (quotientStep_mapped_iff _).mpr raw
  have compared := IntrinsicScopedLocalPolynomial.mapInstance_conclusion rules projection lifted
  have remapped : IntrinsicScopedLocalPolynomial.mapInstance rules projection lifted = occurrence :=
    map_liftOccurrence occurrence
  rw [remapped] at compared
  exact (congrArg quotientStep compared).mpr result

/-- Whole trees in the actual equation-quotient model have runtime witnesses
at their supplied class endpoints. -/
theorem quotientTree_sound (judgment : Judgment algebra)
    (tree : Tree rules algebra judgment) : quotientStep judgment := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate
    (IntrinsicScopedLocalPolynomial.rules rules algebra)
    (fun _ j _ => quotientStep j) ?_ () judgment tree
  intro base j shape descendants premises
  obtain ⟨occurrence, same⟩ := shape
  subst same
  exact quotientStep_ruleClosed occurrence premises

/-- The actual generated firing-tree relation on equation-class states. -/
def ClassReduces {Γ : Ctx signature} (source target : Program Γ) : Prop :=
  Nonempty (Tree rules algebra
    (mapJudgment projection
      (⟨Γ, Srt.tm, source, target⟩ : Judgment (BindingCloneAlgebra.terms signature))))

/-- Every supplied runtime step has a generated quotient-model event. -/
theorem stepModulo_complete {Γ : Ctx signature} {source target : Program Γ}
    (step : StepModulo source target) : ClassReduces source target := by
  obtain ⟨redex, reduct, before, ⟨firing⟩, after⟩ := step
  obtain ⟨tree⟩ := active_complete firing
  have generated : ClassReduces redex reduct :=
    ⟨IntrinsicScopedLocalPolynomial.mapTree rules projection _ tree⟩
  have start : projection.raw.map source = projection.raw.map redex :=
    Quotient.sound (staticEq_complete before)
  have finish : projection.raw.map reduct = projection.raw.map target :=
    Quotient.sound (staticEq_complete after)
  unfold ClassReduces at generated ⊢
  simp only [mapJudgment] at generated ⊢
  rw [start, ← finish]
  exact generated

/-- Exact runtime adequacy of the genuinely classified authored profile,
including arbitrary quotient-valued rule assignments and reference scopes. -/
theorem classReduces_iff_stepModulo {Γ : Ctx signature} (source target : Program Γ) :
    ClassReduces source target ↔ StepModulo source target := by
  constructor
  · rintro ⟨tree⟩
    exact (quotientStep_mapped_iff _).mp (quotientTree_sound _ tree)
  · exact stepModulo_complete

/-- The existing cocontinuous generic reduction, interpreted at the actual
authored program sections, is precisely the runtime step modulo its equations. -/
theorem extension_iff_stepModulo {Γ : Ctx signature} (source target : Program Γ) :
    IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations source target ↔
      StepModulo source target :=
  (IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree rules equations source target).trans
    (classReduces_iff_stepModulo source target)

end Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredClassified
