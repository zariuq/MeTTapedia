import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile
import Mettapedia.OSLF.Syntax.IntrinsicScopedAuthoredClassifiedReduction

/-!
# The scoped polyadic runtime in the existing operational classification

The base is the actual equation quotient of the authored presentation.
The operational constructors are the independently authored active profile.
Quotient-valued occurrences lift to raw representatives at their own contexts;
the runtime's equation closure makes the choice irrelevant. This supplies
the comparison with the existing classifying-model construction, rather than
postulating a new operational interpretation as its own specification.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial (Instance Tree)
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile

abbrev algebra := BindingEquationQuotientModel.algebra equations
abbrev projection := BindingEquationQuotientModel.projection equations

/-- These are the existing classification and cocontinuous interpretation
of the actual equation quotient and active operational constructors. -/
abbrev model := IntrinsicScopedAuthoredClassifiedInstance.model rules equations
abbrev classified := IntrinsicScopedAuthoredClassifiedInstance.classified rules equations
abbrev interpretation := IntrinsicScopedAuthoredClassifiedInstance.interpretation rules equations
abbrev restrictionIso := IntrinsicScopedAuthoredClassifiedInstance.restrictionIso rules equations
abbrev recoveredModelIso := IntrinsicScopedAuthoredClassifiedInstance.recoveredModelIso rules equations

/-- Select a representative separately for every value at its actual local
context. The rule index and ambient context do not change. -/
def liftOccurrence (occurrence : Instance rules algebra) :
    Instance rules (BindingCloneAlgebra.terms sig) where
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

theorem stepModulo_parLeft {Γ : Ctx sig} {source target : Proc Γ}
    (frame : Proc Γ) (step : StepModulo source target) :
    StepModulo (par source frame) (par target frame) := by
  obtain ⟨redex, reduct, before, firing, after⟩ := step
  exact ⟨par redex frame, par reduct frame, .par before (.refl frame),
    .parL frame firing, .par after (.refl frame)⟩

theorem stepModulo_parRight {Γ : Ctx sig} {source target : Proc Γ}
    (frame : Proc Γ) (step : StepModulo source target) :
    StepModulo (par frame source) (par frame target) := by
  obtain ⟨redex, reduct, before, firing, after⟩ := step
  exact ⟨par frame redex, par frame reduct, .par (.refl frame) before,
    .parR frame firing, .par (.refl frame) after⟩

theorem stepModulo_scope {Γ : Ctx sig} {source target : Proc (.nm :: Γ)}
    (step : StepModulo source target) : StepModulo (nu source) (nu target) := by
  obtain ⟨redex, reduct, before, firing, after⟩ := step
  exact ⟨nu redex, nu reduct, .nu before, .nu firing, .nu after⟩

def sourceStepModulo : Judgment (BindingCloneAlgebra.terms sig) → Prop
  | ⟨_, .nm, _, _⟩ => False
  | ⟨_, .pr, source, target⟩ => StepModulo source target

/-- The runtime modulo its independently checked static equations is
closed under every constructor of the same active profile. -/
theorem sourceStepModulo_ruleClosed
    (occurrence : Instance rules (BindingCloneAlgebra.terms sig))
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      sourceStepModulo (IntrinsicScopedLocalPolynomial.childJudgment rules
        (BindingCloneAlgebra.terms sig) occurrence position)) :
    sourceStepModulo (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) occurrence) := by
  rcases occurrence with ⟨⟨index, bounded⟩, Γ, valuation, close⟩
  have small : index < 5 := by simpa [rules] using bounded
  interval_cases index
  · let firing : ContextualRootEvents.Instance comm1 Γ := ⟨valuation, close⟩
    change sourceStepModulo (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) (unaryOccurrence firing))
    rw [unary_conclusion]
    change StepModulo firing.source firing.target
    rw [AuthoredCommunication.arbitrary_unary_source, AuthoredCommunication.arbitrary_unary_target]
    exact (Step.comm1 _ _ _).toModulo
  · let firing : ContextualRootEvents.Instance comm2 Γ := ⟨valuation, close⟩
    change sourceStepModulo (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) (binaryOccurrence firing))
    rw [binary_conclusion]
    change StepModulo firing.source firing.target
    rw [AuthoredCommunication.arbitrary_binary_source, AuthoredCommunication.arbitrary_binary_target]
    exact (Step.comm2 _ _ _ _).toModulo
  · have child := children ⟨0, by simp [rules, parLeft]⟩
    rw [child_as_syntax] at child
    change StepModulo (close .pr .zero) (close .pr (.succ .zero)) at child
    rw [conclusion_as_syntax]
    change StepModulo
      (par (close .pr .zero) (close .pr (.succ (.succ .zero))))
      (par (close .pr (.succ .zero)) (close .pr (.succ (.succ .zero))))
    exact stepModulo_parLeft _ child
  · have child := children ⟨0, by simp [rules, parRight]⟩
    rw [child_as_syntax] at child
    change StepModulo (close .pr .zero) (close .pr (.succ .zero)) at child
    rw [conclusion_as_syntax]
    change StepModulo
      (par (close .pr (.succ (.succ .zero))) (close .pr .zero))
      (par (close .pr (.succ (.succ .zero))) (close .pr (.succ .zero)))
    exact stepModulo_parRight _ child
  · have normalized :
        (⟨⟨4, bounded⟩, Γ, valuation, close⟩ : Instance rules (BindingCloneAlgebra.terms sig)) =
          scopeOccurrence (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)) := by
      have values : valuation = scopeSupply
          (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)) := by
        funext index
        rcases index with ⟨index, bound⟩
        have small : index < 2 := bound
        interval_cases index <;> rfl
      calc
        _ = (⟨⟨4, bounded⟩, Γ,
          scopeSupply (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)),
          close⟩ : Instance rules (BindingCloneAlgebra.terms sig)) :=
          congrArg (fun assigned =>
            (⟨⟨4, bounded⟩, Γ, assigned, close⟩ : Instance rules (BindingCloneAlgebra.terms sig))) values
        _ = _ := by
          unfold scopeOccurrence
          congr 1
          funext s x
          nomatch x
    rw [normalized] at children ⊢
    have child := children ⟨0, by simp [rules, scopeOccurrence, underScope]⟩
    have actual : StepModulo (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)) :=
      (congrArg sourceStepModulo
        (scope_child _ _ ⟨0, by simp [rules, scopeOccurrence, underScope]⟩)).mp child
    exact (congrArg sourceStepModulo (scope_conclusion _ _)).mpr (stepModulo_scope actual)

/-- Replace both supplied endpoints by structurally equal representatives. -/
theorem stepModulo_of_equivalent {Γ : Ctx sig}
    {source source' target target' : Proc Γ}
    (before : StructuralEq source source') (after : StructuralEq target' target)
    (step : StepModulo source' target') : StepModulo source target := by
  obtain ⟨redex, reduct, start, firing, finish⟩ := step
  exact ⟨redex, reduct, .trans before start, firing, .trans finish after⟩

/-- Runtime reduction on quotient judgments, read using arbitrary quotient
representatives. The following lemma proves that those choices do not affect
the supplied raw endpoints. -/
def quotientStep : Judgment algebra → Prop
  | ⟨_, .nm, _, _⟩ => False
  | ⟨_, .pr, source, target⟩ => StepModulo (Quotient.out source) (Quotient.out target)

theorem quotientStep_mapped_iff (judgment : Judgment (BindingCloneAlgebra.terms sig)) :
    quotientStep (mapJudgment projection judgment) ↔ sourceStepModulo judgment := by
  rcases judgment with ⟨Γ, sort, source, target⟩
  cases sort with
  | nm => rfl
  | pr =>
      have sourceEqual : StructuralEq
          (Quotient.out (Quotient.mk _ source : TermQ equations Γ Srt.pr)) source :=
        eqClosure_sound (show EqClosure equations
          (Quotient.out (Quotient.mk _ source : TermQ equations Γ Srt.pr)) source from
          Quotient.exact (Quotient.out_eq (Quotient.mk _ source : TermQ equations Γ Srt.pr)))
      have targetEqual : StructuralEq
          (Quotient.out (Quotient.mk _ target : TermQ equations Γ Srt.pr)) target :=
        eqClosure_sound (show EqClosure equations
          (Quotient.out (Quotient.mk _ target : TermQ equations Γ Srt.pr)) target from
          Quotient.exact (Quotient.out_eq (Quotient.mk _ target : TermQ equations Γ Srt.pr)))
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
        (BindingCloneAlgebra.terms sig) lifted position) := by
    intro position
    have compared : IntrinsicScopedLocalPolynomial.childJudgment rules algebra occurrence position =
        mapJudgment projection (IntrinsicScopedLocalPolynomial.childJudgment rules
          (BindingCloneAlgebra.terms sig) lifted position) := by
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
def ClassReduces {Γ : Ctx sig} (source target : Proc Γ) : Prop :=
  Nonempty (Tree rules algebra
    (mapJudgment projection
      (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig))))

/-- Every supplied runtime step has a generated quotient-model event. -/
theorem stepModulo_complete {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) : ClassReduces source target := by
  obtain ⟨redex, reduct, before, firing, after⟩ := step
  obtain ⟨tree⟩ := step_complete firing
  have generated : ClassReduces redex reduct :=
    ⟨IntrinsicScopedLocalPolynomial.mapTree rules projection _ tree⟩
  have start : projection.raw.map source = projection.raw.map redex :=
    Quotient.sound (structuralEq_complete before)
  have finish : projection.raw.map reduct = projection.raw.map target :=
    Quotient.sound (structuralEq_complete after)
  unfold ClassReduces at generated ⊢
  simp only [mapJudgment] at generated ⊢
  rw [start, ← finish]
  exact generated

/-- Exact runtime adequacy of the genuinely classified authored profile,
including arbitrary quotient-valued rule assignments and private scopes. -/
theorem classReduces_iff_stepModulo {Γ : Ctx sig} (source target : Proc Γ) :
    ClassReduces source target ↔ StepModulo source target := by
  constructor
  · rintro ⟨tree⟩
    exact (quotientStep_mapped_iff _).mp (quotientTree_sound _ tree)
  · exact stepModulo_complete

/-- The existing cocontinuous generic reduction, interpreted at the actual
authored program sections, is precisely the runtime step modulo its equations. -/
theorem extension_iff_stepModulo {Γ : Ctx sig} (source target : Proc Γ) :
    IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations source target ↔
      StepModulo source target :=
  (IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree rules equations source target).trans
    (classReduces_iff_stepModulo source target)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified
