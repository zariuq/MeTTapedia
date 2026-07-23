import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness

/-!
# Finite presentations of binding equation systems

An ordinary HE binding record is a finite first-order equation system.  This
module presents that whole system by one normal finite type substitution.
The construction uses the exact syntactic presentation matcher, not the
gradual type-matching lane, so `%Undefined%` and `Atom` remain ordinary
symbols here.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness

/-- Atom-valued equations denoted by an HE binding record. -/
def bindingAtomEquations (bindings : Bindings) : List (Atom × Atom) :=
  bindings.assignments.map (fun entry => (.var entry.1, entry.2)) ++
    bindings.equalities.map (fun edge => (.var edge.1, .var edge.2))

/-- Native binding satisfaction is pointwise satisfaction of its atom-valued
equation list. -/
theorem typeBindingSatisfied_iff_equations
    (valuation : String → Atom) (bindings : Bindings) :
    TypeBindingSatisfied valuation bindings ↔
      ∀ equation ∈ bindingAtomEquations bindings,
        applyTypeValuation valuation equation.1 =
          applyTypeValuation valuation equation.2 := by
  constructor
  · intro satisfied equation member
    rcases List.mem_append.mp member with assignment | equality
    · obtain ⟨⟨name, value⟩, assignmentMember, rfl⟩ :=
        List.mem_map.mp assignment
      simpa [applyTypeValuation] using
        satisfied.1 name value assignmentMember
    · obtain ⟨⟨left, right⟩, equalityMember, rfl⟩ :=
        List.mem_map.mp equality
      simpa [applyTypeValuation] using
        satisfied.2 left right equalityMember
  · intro equations
    constructor
    · intro name value member
      have equation := equations (.var name, value) (by
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨(name, value), member, rfl⟩)
      simpa [applyTypeValuation] using equation
    · intro left right member
      have equation := equations (.var left, .var right) (by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨(left, right), member, rfl⟩)
      simpa [applyTypeValuation] using equation

/-- Left-to-right presentation of an ordered finite equation system. -/
inductive EquationListPresentationRel :
    List (Atom × Atom) → TypeSubst → TypeSubst → Prop where
  | nil (incoming : TypeSubst) :
      EquationListPresentationRel [] incoming incoming
  | cons {equation : Atom × Atom} {equations : List (Atom × Atom)}
      {incoming next output : TypeSubst} :
      AppliedTypePresentationMatchRel
        incoming equation.1 equation.2 next →
      EquationListPresentationRel equations next output →
      EquationListPresentationRel (equation :: equations) incoming output

/-- A normal incoming presentation stays normal across an equation fold. -/
theorem EquationListPresentationRel.output_normal
    {equations : List (Atom × Atom)} {incoming output : TypeSubst}
    (derivation : EquationListPresentationRel equations incoming output)
    (normal : incoming.Normal) : output.Normal := by
  induction derivation with
  | nil => exact normal
  | cons head _tail inductionHypothesis =>
      exact inductionHypothesis (head.output_normal normal)

/-- The equation fold presents exactly the conjunction of its incoming
theory and every ordered equation. -/
theorem EquationListPresentationRel.solutions
    {equations : List (Atom × Atom)} {incoming output : TypeSubst}
    (derivation : EquationListPresentationRel equations incoming output)
    (normal : incoming.Normal) (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation incoming ∧
        ∀ equation ∈ equations,
          applyTypeValuation valuation equation.1 =
            applyTypeValuation valuation equation.2 := by
  induction derivation with
  | nil => simp
  | @cons equation equations incoming next output head tail
      inductionHypothesis =>
      have nextNormal := head.output_normal normal
      rw [inductionHypothesis nextNormal,
        MatchSolutionTheory.AppliedTypePresentationMatchRel.solutions
          head normal valuation]
      constructor
      · rintro ⟨⟨incomingSatisfied, headEquation⟩, tailEquations⟩
        refine ⟨incomingSatisfied, ?_⟩
        intro current member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact headEquation
        · exact tailEquations current tailMember
      · rintro ⟨incomingSatisfied, allEquations⟩
        exact ⟨⟨incomingSatisfied,
          allEquations equation List.mem_cons_self⟩,
          fun current member =>
            allEquations current (List.mem_cons_of_mem _ member)⟩

/-- Every satisfiable ordered equation system has a normal exact finite
presentation extending the incoming normal presentation. -/
theorem EquationListPresentationRel.exists_of_satisfied
    {valuation : String → Atom} {incoming : TypeSubst}
    (normal : incoming.Normal)
    (incomingSatisfied : TypeSubstSatisfied valuation incoming) :
    ∀ {equations : List (Atom × Atom)},
      (∀ equation ∈ equations,
        applyTypeValuation valuation equation.1 =
          applyTypeValuation valuation equation.2) →
      ∃ output,
        EquationListPresentationRel equations incoming output ∧
          output.Normal ∧ TypeSubstSatisfied valuation output := by
  intro equations equationsSatisfied
  induction equations generalizing incoming with
  | nil => exact ⟨incoming, .nil incoming, normal, incomingSatisfied⟩
  | cons equation equations inductionHypothesis =>
      obtain ⟨next, head, nextNormal, nextSatisfied⟩ :=
        AppliedTypePresentationMatchRel.exists_of_satisfied
          normal incomingSatisfied equation.1 equation.2
            (equationsSatisfied equation List.mem_cons_self)
      obtain ⟨output, tail, outputNormal, outputSatisfied⟩ :=
        inductionHypothesis nextNormal nextSatisfied
          (fun current member => equationsSatisfied current
            (List.mem_cons_of_mem _ member))
      exact ⟨output, .cons head tail, outputNormal, outputSatisfied⟩

/-- Every satisfiable finite HE binding theory has a normal finite
presentation with exactly the same native solution set. -/
theorem exists_normal_exact_presentation
    {bindings : Bindings}
    (satisfiable : ∃ valuation, TypeBindingSatisfied valuation bindings) :
    ∃ presentation,
      presentation.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentation ↔
            TypeBindingSatisfied valuation bindings := by
  obtain ⟨valuation, satisfied⟩ := satisfiable
  have equationsSatisfied :=
    (typeBindingSatisfied_iff_equations valuation bindings).mp satisfied
  obtain ⟨presentation, derivation, normal, _presentationSatisfied⟩ :=
    EquationListPresentationRel.exists_of_satisfied
      TypeSubst.normal_empty (by simp [TypeSubstSatisfied])
        equationsSatisfied
  refine ⟨presentation, normal, ?_⟩
  intro other
  rw [derivation.solutions TypeSubst.normal_empty,
    typeBindingSatisfied_iff_equations]
  simp [TypeSubstSatisfied]

/-! ## Boundary examples -/

/-- Positive: a mixed assignment/equality theory has an exact normal finite
presentation. -/
theorem mixed_binding_theory_presentable :
    ∃ presentation,
      presentation.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentation ↔
            TypeBindingSatisfied valuation
              (⟨[("x", .symbol "A")], [("y", "z")]⟩ : Bindings) := by
  apply exists_normal_exact_presentation
  refine ⟨fun name => if name = "x" then .symbol "A" else .symbol "C", ?_⟩
  constructor
  · intro name value member
    simp at member
    rcases member with ⟨rfl, rfl⟩
    simp [applyTypeValuation]
  · intro left right member
    simp at member
    rcases member with ⟨rfl, rfl⟩
    simp

/-- Negative: the inconsistent equation `$x = A` and `$x = B` has no
satisfying valuation. -/
theorem incompatible_binding_theory_not_satisfiable :
    ¬∃ valuation,
      TypeBindingSatisfied valuation
        (⟨[("x", .symbol "A"), ("x", .symbol "B")], []⟩ : Bindings) := by
  rintro ⟨valuation, satisfied⟩
  have first := satisfied.1 "x" (.symbol "A") (by simp)
  have second := satisfied.1 "x" (.symbol "B") (by simp)
  simp [applyTypeValuation] at first second
  have impossible : (Atom.symbol "A") = .symbol "B" :=
    first.symm.trans second
  simp at impossible

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
