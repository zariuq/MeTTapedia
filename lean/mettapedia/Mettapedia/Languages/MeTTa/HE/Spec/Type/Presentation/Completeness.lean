import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory

/-!
# Completeness of finite type presentations

Every satisfiable finite type-equation step has a normal, finite
presentation.  The proof follows the declarative matcher itself.  Its
well-founded measure is the size of the two atoms after applying a satisfying
valuation; this measure is invariant under presentation extension and drops
strictly when an expression is decomposed.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Theory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.MatchSolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement

private theorem atom_size_pos (atom : Atom) : 0 < sizeOf atom := by
  cases atom <;> simp

private theorem atom_size_lt_expression_of_mem
    {atom : Atom} {atoms : List Atom} (member : atom ∈ atoms) :
    sizeOf atom < sizeOf (.expression atoms : Atom) := by
  induction atoms with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp
        omega
      · have smaller := ih member
        simp at smaller ⊢
        omega

mutual

private theorem valuation_image_size_le_of_typeVar
    (valuation : String → Atom) (atom : Atom) {name : String}
    (member : name ∈ TypeSubst.typeVars atom) :
    sizeOf (valuation name) ≤
      sizeOf (applyTypeValuation valuation atom) := by
  cases atom with
  | symbol symbol => simp [TypeSubst.typeVars] at member
  | var variableName =>
      simp [TypeSubst.typeVars] at member
      subst variableName
      simp [applyTypeValuation]
  | grounded value => simp [TypeSubst.typeVars] at member
  | expression atoms =>
      simpa [applyTypeValuation] using Nat.le_of_lt
        (valuation_image_size_lt_expression_of_typeVar valuation atoms member)
termination_by 2 * sizeOf atom

private theorem valuation_image_size_lt_expression_of_typeVar
    (valuation : String → Atom) (atoms : List Atom) {name : String}
    (member : name ∈ TypeSubst.typeVarsList atoms) :
    sizeOf (valuation name) <
      sizeOf (.expression
        (atoms.map (applyTypeValuation valuation)) : Atom) := by
  cases atoms with
  | nil => simp [TypeSubst.typeVarsList] at member
  | cons head tail =>
      simp only [TypeSubst.typeVarsList, List.mem_append] at member
      rcases member with headMember | tailMember
      · have headLe :=
          valuation_image_size_le_of_typeVar valuation head headMember
        have headMem : applyTypeValuation valuation head ∈
            (head :: tail).map (applyTypeValuation valuation) := by simp
        exact lt_of_le_of_lt headLe
          (atom_size_lt_expression_of_mem headMem)
      · have tailLt :=
          valuation_image_size_lt_expression_of_typeVar
            valuation tail tailMember
        simp at tailLt ⊢
        omega
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

end

/-- A satisfiable nontrivial variable equation passes the finite occurs check.
If the variable occurred properly in its right side, its valuation image would
be a proper subterm of itself. -/
theorem typeVar_not_mem_of_satisfied
    {valuation : String → Atom} {name : String} {atom : Atom}
    (equation : valuation name = applyTypeValuation valuation atom)
    (nontrivial : atom ≠ .var name) :
    name ∉ TypeSubst.typeVars atom := by
  intro occurs
  cases atom with
  | symbol symbol => simp [TypeSubst.typeVars] at occurs
  | grounded value => simp [TypeSubst.typeVars] at occurs
  | var other =>
      simp [TypeSubst.typeVars] at occurs
      exact nontrivial (by simp [occurs])
  | expression atoms =>
      have imageLt :=
        valuation_image_size_lt_expression_of_typeVar valuation atoms occurs
      have imageEq := congrArg sizeOf equation
      simp only [applyTypeValuation] at imageLt imageEq
      rw [← imageEq] at imageLt
      omega

@[simp] private theorem size_apply_eq_of_satisfied
    {valuation : String → Atom} {substitution : TypeSubst}
    (satisfied : TypeSubstSatisfied valuation substitution)
    (atom : Atom) :
    sizeOf (applyTypeValuation valuation (substitution.apply atom)) =
      sizeOf (applyTypeValuation valuation atom) :=
  congrArg sizeOf (satisfied.absorbs atom)

private abbrev AppliedComplete
    (valuation : String → Atom) (substitution : TypeSubst)
    (left right : Atom) : Prop :=
  ∃ output,
    AppliedReducedTypeMatchRel substitution left right output ∧
      output.Normal ∧ TypeSubstSatisfied valuation output

private abbrev AppliedPresentationComplete
    (valuation : String → Atom) (substitution : TypeSubst)
    (left right : Atom) : Prop :=
  ∃ output,
    AppliedTypePresentationMatchRel substitution left right output ∧
      output.Normal ∧ TypeSubstSatisfied valuation output

private abbrev AppliedListComplete
    (valuation : String → Atom) (substitution : TypeSubst)
    (left right : List Atom) : Prop :=
  ∃ output,
    AppliedReducedTypeListMatchRel substitution left right output ∧
      output.Normal ∧ TypeSubstSatisfied valuation output

set_option maxHeartbeats 1000000 in
mutual

private theorem applied_complete
    (valuation : String → Atom) {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : Atom)
    (leftFixed : substitution.apply left = left)
    (rightFixed : substitution.apply right = right)
    (equation : applyTypeValuation valuation left =
      applyTypeValuation valuation right) :
    AppliedComplete valuation substitution left right := by
  by_cases same : left = right
  · subst right
    exact ⟨substitution, .identical substitution left, normal, satisfied⟩
  cases left with
  | var name =>
      have nontrivial : right ≠ .var name := by
        intro equality
        exact same equality.symm
      have occursClean : name ∉ TypeSubst.typeVars right :=
        typeVar_not_mem_of_satisfied
          (by simpa [applyTypeValuation] using equation) nontrivial
      have unassigned : substitution.lookup name = none :=
        lookup_eq_none_of_apply_var_eq_self normal leftFixed
      refine ⟨substitution.bind name right,
        .bindLeft occursClean, ?_, ?_⟩
      · apply normal.bind
        simpa [rightFixed] using occursClean
      · exact (TypeSubstSatisfied.bind_iff unassigned valuation).mpr
          ⟨satisfied, by
            simpa [applyTypeValuation] using equation⟩
  | symbol leftName =>
      cases right with
      | var name =>
          have notVariable : ∀ other, (.symbol leftName : Atom) ≠ .var other :=
            fun _ => by simp
          have occursClean : name ∉ TypeSubst.typeVars (.symbol leftName) := by
            simp [TypeSubst.typeVars]
          have unassigned : substitution.lookup name = none :=
            lookup_eq_none_of_apply_var_eq_self normal rightFixed
          refine ⟨substitution.bind name (.symbol leftName),
            .bindRight notVariable occursClean, ?_, ?_⟩
          · apply normal.bind
            simpa [leftFixed] using occursClean
          · exact (TypeSubstSatisfied.bind_iff unassigned valuation).mpr
              ⟨satisfied, by
                simpa [applyTypeValuation] using equation.symm⟩
      | symbol rightName =>
          have names : leftName = rightName := by
            simpa [applyTypeValuation] using equation
          subst rightName
          exact (same rfl).elim
      | grounded rightValue => simp [applyTypeValuation] at equation
      | expression rightAtoms => simp [applyTypeValuation] at equation
  | grounded leftValue =>
      cases right with
      | var name =>
          have notVariable : ∀ other,
              (.grounded leftValue : Atom) ≠ .var other := fun _ => by simp
          have occursClean :
              name ∉ TypeSubst.typeVars (.grounded leftValue) := by
            simp [TypeSubst.typeVars]
          have unassigned : substitution.lookup name = none :=
            lookup_eq_none_of_apply_var_eq_self normal rightFixed
          refine ⟨substitution.bind name (.grounded leftValue),
            .bindRight notVariable occursClean, ?_, ?_⟩
          · apply normal.bind
            simpa [leftFixed] using occursClean
          · exact (TypeSubstSatisfied.bind_iff unassigned valuation).mpr
              ⟨satisfied, by
                simpa [applyTypeValuation] using equation.symm⟩
      | symbol rightName => simp [applyTypeValuation] at equation
      | grounded rightValue =>
          have values : leftValue = rightValue := by
            simpa [applyTypeValuation] using equation
          subst rightValue
          exact (same rfl).elim
      | expression rightAtoms => simp [applyTypeValuation] at equation
  | expression leftAtoms =>
      cases right with
      | var name =>
          have notVariable : ∀ other,
              (.expression leftAtoms : Atom) ≠ .var other := fun _ => by simp
          have occursClean :
              name ∉ TypeSubst.typeVars (.expression leftAtoms) :=
            typeVar_not_mem_of_satisfied
              (by simpa [applyTypeValuation] using equation.symm) (by simp)
          have unassigned : substitution.lookup name = none :=
            lookup_eq_none_of_apply_var_eq_self normal rightFixed
          refine ⟨substitution.bind name (.expression leftAtoms),
            .bindRight notVariable occursClean, ?_, ?_⟩
          · apply normal.bind
            simpa [leftFixed] using occursClean
          · exact (TypeSubstSatisfied.bind_iff unassigned valuation).mpr
              ⟨satisfied, by
                simpa [applyTypeValuation] using equation.symm⟩
      | symbol rightName => simp [applyTypeValuation] at equation
      | grounded rightValue => simp [applyTypeValuation] at equation
      | expression rightAtoms =>
          have listEquation :
              leftAtoms.map (applyTypeValuation valuation) =
                rightAtoms.map (applyTypeValuation valuation) := by
            simpa [applyTypeValuation] using equation
          have measureDecrease :
              5 *
                    (sizeOf (leftAtoms.map (applyTypeValuation valuation)) +
                      sizeOf (rightAtoms.map
                        (applyTypeValuation valuation))) + 2 <
                5 *
                  (sizeOf (applyTypeValuation valuation
                      (.expression leftAtoms)) +
                    sizeOf (applyTypeValuation valuation
                      (.expression rightAtoms))) := by
            simp [applyTypeValuation]
            omega
          obtain ⟨output, children, outputNormal, outputSatisfied⟩ :=
            applied_list_complete valuation normal satisfied
              leftAtoms rightAtoms listEquation
          exact ⟨output, .expression children,
            outputNormal, outputSatisfied⟩
termination_by 5 *
  (sizeOf (applyTypeValuation valuation left) +
    sizeOf (applyTypeValuation valuation right))

private theorem applied_presentation_complete
    (valuation : String → Atom) {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : Atom)
    (equation : applyTypeValuation valuation left =
      applyTypeValuation valuation right) :
    AppliedPresentationComplete valuation substitution left right := by
  let resolvedLeft := substitution.apply left
  let resolvedRight := substitution.apply right
  have resolvedEquation :
      applyTypeValuation valuation resolvedLeft =
        applyTypeValuation valuation resolvedRight := by
    dsimp [resolvedLeft, resolvedRight]
    rw [satisfied.absorbs left, satisfied.absorbs right]
    exact equation
  have leftFixed : substitution.apply resolvedLeft = resolvedLeft := by
    dsimp [resolvedLeft]
    exact normal.apply_idempotent left
  have rightFixed : substitution.apply resolvedRight = resolvedRight := by
    dsimp [resolvedRight]
    exact normal.apply_idempotent right
  have measureNonincrease :
      sizeOf (applyTypeValuation valuation (substitution.apply left)) +
          sizeOf (applyTypeValuation valuation (substitution.apply right)) ≤
        sizeOf (applyTypeValuation valuation left) +
          sizeOf (applyTypeValuation valuation right) := by
    rw [size_apply_eq_of_satisfied satisfied left,
      size_apply_eq_of_satisfied satisfied right]
  obtain ⟨output, applied, outputNormal, outputSatisfied⟩ :=
    applied_complete valuation normal satisfied resolvedLeft resolvedRight
      leftFixed rightFixed resolvedEquation
  exact ⟨output, .ordinary rfl rfl applied,
    outputNormal, outputSatisfied⟩
termination_by 5 *
  (sizeOf (applyTypeValuation valuation left) +
    sizeOf (applyTypeValuation valuation right)) + 1

private theorem applied_list_complete
    (valuation : String → Atom) {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : List Atom)
    (equation : left.map (applyTypeValuation valuation) =
      right.map (applyTypeValuation valuation)) :
    AppliedListComplete valuation substitution left right := by
  cases left with
  | nil =>
      cases right with
      | nil => exact ⟨substitution, .nil substitution, normal, satisfied⟩
      | cons rightHead rightTail => simp at equation
  | cons leftHead leftTail =>
      cases right with
      | nil => simp at equation
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at equation
          obtain ⟨next, head, nextNormal, nextSatisfied⟩ :=
            applied_presentation_complete valuation normal satisfied
              leftHead rightHead equation.1
          obtain ⟨output, tail, outputNormal, outputSatisfied⟩ :=
            applied_list_complete valuation nextNormal nextSatisfied
              leftTail rightTail equation.2
          exact ⟨output, .cons head tail,
            outputNormal, outputSatisfied⟩
termination_by 5 *
  (sizeOf (left.map (applyTypeValuation valuation)) +
    sizeOf (right.map (applyTypeValuation valuation))) + 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals dsimp at *
  all_goals simp_all
  all_goals omega

end

private abbrev ReducedComplete
    (valuation : String → Atom) (substitution : TypeSubst)
    (left right : Atom) : Prop :=
  ∃ output,
    ReducedTypePresentationMatchRel substitution left right output ∧
      output.Normal ∧ TypeSubstSatisfied valuation output

private abbrev ReducedListComplete
    (valuation : String → Atom) (substitution : TypeSubst)
    (left right : List Atom) : Prop :=
  ∃ output,
    ReducedTypePresentationListMatchRel substitution left right output ∧
      output.Normal ∧ TypeSubstSatisfied valuation output

mutual

private theorem reduced_complete
    (valuation : String → Atom) {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : Atom)
    (consistent : ReducedTypeConsistent valuation left right) :
    ReducedComplete valuation substitution left right := by
  by_cases leftUndefined : left = Atom.undefinedType
  · subst left
    exact ⟨substitution, .undefinedLeft substitution right,
      normal, satisfied⟩
  by_cases rightUndefined : right = Atom.undefinedType
  · subst right
    exact ⟨substitution, .undefinedRight substitution left,
      normal, satisfied⟩
  by_cases expressions : ∃ lefts rights,
      left = .expression lefts ∧ right = .expression rights
  · obtain ⟨lefts, rights, rfl, rfl⟩ := expressions
    have listConsistent :
        ReducedTypeListConsistent valuation lefts rights := by
      simpa [ReducedTypeConsistent] using consistent
    obtain ⟨output, children, outputNormal, outputSatisfied⟩ :=
      reduced_list_complete valuation normal satisfied
        lefts rights listConsistent
    exact ⟨output, .expression children,
      outputNormal, outputSatisfied⟩
  · have leafShape : ReducedTypeLeafShape left right := by
      cases left <;> cases right
      all_goals simp [ReducedTypeLeafShape]
      exact expressions ⟨_, _, rfl, rfl⟩
    have equation :
        applyTypeValuation valuation left =
          applyTypeValuation valuation right :=
      (reducedTypeConsistent_iff_applied_eq_of_leaf
        valuation left right leafShape leftUndefined rightUndefined).mp
          consistent
    let resolvedLeft := substitution.apply left
    let resolvedRight := substitution.apply right
    have resolvedEquation :
        applyTypeValuation valuation resolvedLeft =
          applyTypeValuation valuation resolvedRight := by
      dsimp [resolvedLeft, resolvedRight]
      rw [satisfied.absorbs left, satisfied.absorbs right]
      exact equation
    have leftFixed : substitution.apply resolvedLeft = resolvedLeft := by
      dsimp [resolvedLeft]
      exact normal.apply_idempotent left
    have rightFixed : substitution.apply resolvedRight = resolvedRight := by
      dsimp [resolvedRight]
      exact normal.apply_idempotent right
    obtain ⟨output, applied, outputNormal, outputSatisfied⟩ :=
      applied_complete valuation normal satisfied resolvedLeft resolvedRight
        leftFixed rightFixed resolvedEquation
    exact ⟨output,
      .ordinary leftUndefined rightUndefined leafShape rfl rfl applied,
      outputNormal, outputSatisfied⟩
termination_by 2 * (sizeOf left + sizeOf right)

private theorem reduced_list_complete
    (valuation : String → Atom) {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : List Atom)
    (consistent : ReducedTypeListConsistent valuation left right) :
    ReducedListComplete valuation substitution left right := by
  cases left with
  | nil =>
      cases right with
      | nil => exact ⟨substitution, .nil substitution, normal, satisfied⟩
      | cons rightHead rightTail =>
          simp [ReducedTypeListConsistent] at consistent
  | cons leftHead leftTail =>
      cases right with
      | nil => simp [ReducedTypeListConsistent] at consistent
      | cons rightHead rightTail =>
          simp only [ReducedTypeListConsistent] at consistent
          obtain ⟨next, head, nextNormal, nextSatisfied⟩ :=
            reduced_complete valuation normal satisfied
              leftHead rightHead consistent.1
          obtain ⟨output, tail, outputNormal, outputSatisfied⟩ :=
            reduced_list_complete valuation nextNormal nextSatisfied
              leftTail rightTail consistent.2
          exact ⟨output, .cons head tail,
            outputNormal, outputSatisfied⟩
termination_by 2 * (sizeOf left + sizeOf right) + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

end

/-- Completeness of ordinary syntactic presentation matching.  Any model of
the incoming normal presentation that equates two atoms yields a normal
finite output presentation satisfied by the same model.  This is the exact
equation lane: gradual type wildcards play no role. -/
theorem AppliedTypePresentationMatchRel.exists_of_satisfied
    {valuation : String → Atom} {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : Atom)
    (equation : applyTypeValuation valuation left =
      applyTypeValuation valuation right) :
    ∃ output,
      AppliedTypePresentationMatchRel substitution left right output ∧
        output.Normal ∧ TypeSubstSatisfied valuation output :=
  applied_presentation_complete valuation normal satisfied left right equation

/-- Completeness of the raw R2 presentation lane.  Any valuation satisfying
the incoming normal presentation and the recursive reduced-type consistency
produces a normal output presentation satisfying the same valuation. -/
theorem ReducedTypePresentationMatchRel.exists_of_satisfied
    {valuation : String → Atom} {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : Atom)
    (consistent : ReducedTypeConsistent valuation left right) :
    ∃ output,
      ReducedTypePresentationMatchRel substitution left right output ∧
        output.Normal ∧ TypeSubstSatisfied valuation output :=
  reduced_complete valuation normal satisfied left right consistent

/-- Completeness of published top-level gradual matching plus the named R2
refinement.  This is the presentation-existence boundary needed to turn the
already sealed solution theory into an exact inferred return package. -/
theorem CorePlusR2TypePresentationMatchRel.exists_of_satisfied
    {valuation : String → Atom} {substitution : TypeSubst}
    (normal : substitution.Normal)
    (satisfied : TypeSubstSatisfied valuation substitution)
    (left right : Atom)
    (consistent : CorePlusR2TypeConsistent valuation left right) :
    ∃ output,
      CorePlusR2TypePresentationMatchRel substitution left right output ∧
        output.Normal ∧ TypeSubstSatisfied valuation output := by
  by_cases leftUndefined : left = Atom.undefinedType
  · subst left
    exact ⟨substitution, .undefinedLeft substitution right,
      normal, satisfied⟩
  by_cases rightUndefined : right = Atom.undefinedType
  · subst right
    exact ⟨substitution, .undefinedRight substitution left,
      normal, satisfied⟩
  by_cases leftAtom : left = Atom.atomType
  · subst left
    exact ⟨substitution, .atomLeft substitution right,
      normal, satisfied⟩
  by_cases rightAtom : right = Atom.atomType
  · subst right
    exact ⟨substitution, .atomRight substitution left,
      normal, satisfied⟩
  have reduced : ReducedTypeConsistent valuation left right := by
    simpa [CorePlusR2TypeConsistent, leftUndefined, rightUndefined,
      leftAtom, rightAtom] using consistent
  obtain ⟨output, derivation, outputNormal, outputSatisfied⟩ :=
    reduced_complete valuation normal satisfied left right reduced
  exact ⟨output,
    .reduced leftUndefined rightUndefined leftAtom rightAtom derivation,
    outputNormal, outputSatisfied⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Completeness
