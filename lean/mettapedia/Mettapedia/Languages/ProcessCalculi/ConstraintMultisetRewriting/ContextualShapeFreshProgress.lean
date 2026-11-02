import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapePotential
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationActive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairActive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairActive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualHeterogeneousFlexPair

/-!
# Fresh-helper progress from first-order shape models

Imitation splits a constructor image into its fields. A distinct flexible
pair shares one positive image, and same-hole pruning keeps the image while
strictly reducing the parameter interface. Scope is handled by the actual
typed answers; the weights require only their first-order shapes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeFreshProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment
open ContextualShapeErasure
open ContextualActiveSupport
open scoped BigOperators

variable {S : Signature} {V Other Next : Type} {source : V → MetaArity S}

theorem left_active [DecidableEq V] (problem : Problem source) (identity : V) {Γ : Ctx S}
    (rho : Ren S (source identity).1 Γ) (right : Observation S source)
    (selected : (observe (rename (S := signature S source) rho (generator source identity)), right) ∈ problem) :
    identity ∈ active problem := by
  apply (mem_active _ _).mpr
  refine ⟨_, selected, .inl ?_⟩
  change identity ∈ support (rename (S := signature S source) rho (generator source identity))
  rw [support_rename, support_generator]
  exact List.mem_singleton_self _

theorem right_active [DecidableEq V] (problem : Problem source) (identity : V) {Γ : Ctx S}
    (rho : Ren S (source identity).1 Γ) (left : Observation S source)
    (selected : (left, observe (rename (S := signature S source) rho (generator source identity))) ∈ problem) :
    identity ∈ active problem := by
  apply (mem_active _ _).mpr
  refine ⟨_, selected, .inr ?_⟩
  change identity ∈ support (rename (S := signature S source) rho (generator source identity))
  rw [support_rename, support_generator]
  exact List.mem_singleton_self _

def fieldImages (images : ShapeAssignment S (Unit ⊕ Other) Next) {arities : List (MetaArity S)} {Γ : Ctx S}
    {declaration : Unit ⊕ Other → MetaArity S} (fields : Args (signature S declaration) arities Γ) :
    ShapeAssignment S (ArgumentSlots.Slot arities ⊕ Other) Next
  | .inl slot => evaluate images (ArgumentSlots.get fields slot.1 slot.2)
  | .inr identity => images (.inr identity)

theorem field_vector (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) (images : ShapeAssignment S (Unit ⊕ Other) Next)
    {Γ : Ctx S} (fields : Args (signature S (ContextualImitation.sourceDeclarations parameters result others)) (S.arity operator) Γ) :
    evaluateArgs (fieldImages images fields) (ContextualImitation.freshFields parameters operator others) =
      evaluateArgs images fields := by
  funext position
  obtain ⟨slot, rfl⟩ := (ArgumentSlots.indexEquiv (S.arity operator)).surjective position
  change evaluateArgs (fieldImages images fields) (ContextualImitation.freshFields parameters operator others)
    (ArgumentSlots.toIndex slot) = evaluateArgs images fields (ArgumentSlots.toIndex slot)
  rw [evaluateArgs_at_slot, ContextualImitation.freshFields, ArgumentSlots.get_tabulate, evaluate_generator,
    evaluateArgs_at_slot]
  rfl

theorem field_sum {declaration : Unit ⊕ Other → MetaArity S} (images : ShapeAssignment S (Unit ⊕ Other) Next)
    {arities : List (MetaArity S)} {Γ : Ctx S} (fields : Args (signature S declaration) arities Γ) :
    (∑ slot : ArgumentSlots.Slot arities, (fieldImages images fields (.inl slot)).size) =
      ∑ position, (evaluateArgs images fields position).size := by
  apply Fintype.sum_equiv (ArgumentSlots.indexEquiv arities)
  intro slot
  exact congrArg Mettapedia.Logic.LP.Term.size (evaluateArgs_at_slot images fields slot).symm

theorem imitation [DecidableEq Other] (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) {Γ : Ctx S} (rho : Ren S parameters Γ)
    (fields : Args (signature S (ContextualImitation.sourceDeclarations parameters result others)) (S.arity operator) Γ)
    (problem : Problem (ContextualImitation.sourceDeclarations parameters result others))
    (selected : (observe (rename (S := signature S (ContextualImitation.sourceDeclarations parameters result others)) rho
      (generator (ContextualImitation.sourceDeclarations parameters result others) (.inl ()))),
      observe (Term.op (.inl operator) fields)) ∈ problem)
    (images : ShapeAssignment S (Unit ⊕ Other) Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    let answer := ContextualImitation.answer parameters operator others
    let remaining := fieldImages images fields
    ShapeModels remaining (mapProblem answer problem) ∧
      (∀ identity, images identity = evaluate remaining (answer identity)) ∧
      ContextualShapePotential.potential remaining (active (mapProblem answer problem)) <
        ContextualShapePotential.potential images (active problem) := by
  have head := models _ selected
  change evaluate images (rename (S := signature S (ContextualImitation.sourceDeclarations parameters result others)) rho
    (generator (ContextualImitation.sourceDeclarations parameters result others) (.inl ()))) =
      evaluate images (Term.op (.inl operator) fields) at head
  rw [evaluate_rename, evaluate_generator] at head
  let remaining := fieldImages images fields
  have components : ∀ identity, images identity = evaluate remaining
      (ContextualImitation.answer parameters operator others identity) := by
    intro identity
    cases identity with
    | inl marker =>
        cases marker
        change images (.inl ()) = Mettapedia.Logic.LP.Term.app (σ := shapeSignature S Next) ⟨result, operator⟩
          (evaluateArgs remaining (ContextualImitation.freshFields parameters operator others))
        rw [field_vector]
        exact head
    | inr identity => rfl
  refine ⟨(ContextualShapeTransport.models_of_components images _ remaining components problem patterned).mpr models,
    components, ?_⟩
  have root := left_active problem (.inl ()) rho _ selected
  have start := ContextualShapePotential.unit images (active problem) root
  have finish := ContextualShapePotential.monotone remaining (ContextualImitationActive.active_is_bounded parameters operator others problem)
  rw [ContextualImitationActive.targetRoster, ContextualShapePotential.disjSum] at finish
  have sizes := congrArg Mettapedia.Logic.LP.Term.size head
  change (images (.inl ())).size = 1 + ∑ position, (evaluateArgs images fields position).size at sizes
  rw [← field_sum images fields] at sizes
  change (images (.inl ())).size = 1 + ∑ slot, (remaining (.inl slot)).size at sizes
  change _ ≤ (∑ slot : ArgumentSlots.Slot (S.arity operator), (remaining (.inl slot)).size) +
    ∑ identity ∈ (active problem).toRight, (images (.inr identity)).size at finish
  change ContextualShapePotential.potential remaining
    (active (mapProblem (ContextualImitation.answer parameters operator others) problem)) < _
  omega

theorem self [DecidableEq Other] {Δ Γ : Ctx S} (left right : Ren S Δ Γ) (different : left ≠ right)
    (result : S.Srt) (others : Other → MetaArity S) (problem : Problem (ContextualSelfPair.declarations Δ result others))
    (selected : (observe (rename (S := signature S (ContextualSelfPair.declarations Δ result others)) left
      (generator (ContextualSelfPair.declarations Δ result others) (.inl ()))),
      observe (rename (S := signature S (ContextualSelfPair.declarations Δ result others)) right
      (generator (ContextualSelfPair.declarations Δ result others) (.inl ())))) ∈ problem)
    (images : ShapeAssignment S (Unit ⊕ Other) Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    let equalizer := ScopeEqualizer.Finite.build left right
    let answer := ContextualSelfPair.answer equalizer result others
    ShapeModels images (mapProblem answer problem) ∧
      (∀ identity, images identity = evaluate images (answer identity)) ∧
      ContextualShapePotential.potential images (active (mapProblem answer problem)) ≤ ContextualShapePotential.potential images (active problem) ∧
      ContextualInterfacePotential.cost (ContextualSelfPair.declarations equalizer.context result others)
        (active (mapProblem answer problem)) <
          ContextualInterfacePotential.cost (ContextualSelfPair.declarations Δ result others) (active problem) := by
  let equalizer := ScopeEqualizer.Finite.build left right
  let answer := ContextualSelfPair.answer equalizer result others
  have components : ∀ identity, images identity = evaluate images (answer identity) := by
    intro identity
    cases identity with
    | inl marker => simp only [answer, ContextualSelfPair.answer, evaluate_rename, evaluate_generator]
    | inr identity => rfl
  have root := left_active problem (.inl ()) left _ selected
  have bounded := ContextualSelfPairActive.active_is_bounded equalizer result others problem
  have sourceImages := ContextualShapePotential.unit images (active problem) root
  have targetImages := ContextualShapePotential.monotone images bounded
  rw [ContextualSelfPairActive.targetRoster, ContextualShapePotential.disjSum, Finset.sum_singleton] at targetImages
  have sourceParameters := ContextualInterfacePotential.selected_unit_cost Δ result others (active problem) root
  have targetParameters := ContextualInterfacePotential.monotone
    (ContextualSelfPair.declarations equalizer.context result others) bounded
  rw [ContextualSelfPairActive.targetRoster, ContextualInterfacePotential.unit_roster_cost] at targetParameters
  have strict := ScopeEqualizer.Finite.context_length_lt left right different
  refine ⟨(ContextualShapeTransport.models_of_components images answer images components problem patterned).mpr models,
    components, ?_, ?_⟩
  · exact targetImages.trans_eq sourceImages.symm
  · change equalizer.context.length < Δ.length at strict
    change _ ≤ equalizer.context.length + _ at targetParameters
    change ContextualInterfacePotential.cost (ContextualSelfPair.declarations equalizer.context result others)
      (active (mapProblem answer problem)) < ContextualInterfacePotential.cost
        (ContextualSelfPair.declarations Δ result others) (active problem)
    exact (lt_of_le_of_lt targetParameters (Nat.add_lt_add_right strict _)).trans_eq sourceParameters.symm

def commonImages (images : ShapeAssignment S (Bool ⊕ Other) Next) : ShapeAssignment S (Unit ⊕ Other) Next
  | .inl _ => images (.inl false)
  | .inr identity => images (.inr identity)

theorem flex [DecidableEq Other] {L R Γ : Ctx S} {left : Ren S L Γ} {right : Ren S R Γ}
    (pullback : ScopePullback left right) (result : S.Srt) (others : Other → MetaArity S)
    (problem : Problem (ContextualFlexPair.sourceDeclarations L R result others))
    (selected : (observe (rename (S := signature S (ContextualFlexPair.sourceDeclarations L R result others)) left
      (generator (ContextualFlexPair.sourceDeclarations L R result others) (.inl false))),
      observe (rename (S := signature S (ContextualFlexPair.sourceDeclarations L R result others)) right
      (generator (ContextualFlexPair.sourceDeclarations L R result others) (.inl true)))) ∈ problem)
    (images : ShapeAssignment S (Bool ⊕ Other) Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    let answer := ContextualFlexPair.answer pullback result others
    let remaining := commonImages images
    ShapeModels remaining (mapProblem answer problem) ∧
      (∀ identity, images identity = evaluate remaining (answer identity)) ∧
      ContextualShapePotential.potential remaining (active (mapProblem answer problem)) <
        ContextualShapePotential.potential images (active problem) := by
  have head := models _ selected
  change evaluate images (rename (S := signature S (ContextualFlexPair.sourceDeclarations L R result others)) left
    (generator (ContextualFlexPair.sourceDeclarations L R result others) (.inl false))) =
    evaluate images (rename (S := signature S (ContextualFlexPair.sourceDeclarations L R result others)) right
    (generator (ContextualFlexPair.sourceDeclarations L R result others) (.inl true))) at head
  rw [evaluate_rename, evaluate_rename, evaluate_generator, evaluate_generator] at head
  let remaining := commonImages images
  have components : ∀ identity, images identity = evaluate remaining (ContextualFlexPair.answer pullback result others identity) := by
    intro identity
    cases identity with
    | inl marker =>
        cases marker
        · simp only [ContextualFlexPair.answer, evaluate_rename, evaluate_generator, remaining, commonImages]
        · simpa only [ContextualFlexPair.answer, evaluate_rename, evaluate_generator, remaining, commonImages] using head.symm
    | inr identity => rfl
  have first := left_active problem (.inl false) left _ selected
  have second := right_active problem (.inl true) right _ selected
  have start := ContextualShapePotential.pair images (active problem) first second
  have finish := ContextualShapePotential.monotone remaining (ContextualFlexPairActive.active_is_bounded pullback result others problem)
  rw [ContextualFlexPairActive.targetRoster, ContextualShapePotential.disjSum, Finset.sum_singleton] at finish
  have positive := Mettapedia.Logic.LP.Term.size_pos (images (.inl true))
  refine ⟨(ContextualShapeTransport.models_of_components images _ remaining components problem patterned).mpr models, components, ?_⟩
  change _ ≤ (images (.inl false)).size + ∑ identity ∈ (active problem).toRight, (images (.inr identity)).size at finish
  change ContextualShapePotential.potential remaining
    (active (mapProblem (ContextualFlexPair.answer pullback result others) problem)) < _
  omega

theorem heterogeneous_flex [DecidableEq Other] (L R : Ctx S) (first second : S.Srt) (same : first = second)
    (others : Other → MetaArity S) {Γ : Ctx S} (left : Ren S L Γ) (right : Ren S R Γ)
    (problem : Problem (ContextualHeterogeneousFlexPair.declarations L R first second others))
    (selected : (observe (rename (S := signature S (ContextualHeterogeneousFlexPair.declarations L R first second others)) left
      (generator (ContextualHeterogeneousFlexPair.declarations L R first second others) (.inl false))),
      observe (rename (S := signature S (ContextualHeterogeneousFlexPair.declarations L R first second others)) right
      (generator (ContextualHeterogeneousFlexPair.declarations L R first second others) (.inl true)))) ∈ problem)
    (images : ShapeAssignment S (Bool ⊕ Other) Next) (patterned : ProblemPattern problem) (models : ShapeModels images problem) :
    let answer := ContextualHeterogeneousFlexPair.answer L R first second same others left right
    let remaining := commonImages images
    ShapeModels remaining (mapProblem answer problem) ∧
      (∀ identity, images identity = evaluate remaining (answer identity)) ∧
      ContextualShapePotential.potential remaining (active (mapProblem answer problem)) <
        ContextualShapePotential.potential images (active problem) := by
  cases same
  exact flex (ScopePullback.Finite.build left right) first others problem selected images patterned models

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeFreshProgress
