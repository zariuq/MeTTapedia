import Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance
import Mettapedia.Languages.MeTTa.HE.MatchSizeTheory

/-!
# Semantic completeness of the human HE matcher/merge relation

This module constructs human-spec matcher and merger derivations directly
from a common valuation.  The construction is independent of both executable
matchers and both executable binding mergers.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanMatchCompleteness

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private abbrev HumanMatch := HumanMatchMergeSpec.MatchRel
  HumanMatchMergeSpec.equalityGroundedSemantic

private theorem assignmentsNonVariable_empty :
    HEAssignmentsNonVariable Bindings.empty := by
  intro key value hmem
  simp [Bindings.empty] at hmem

/-- A satisfied unequal pair of non-variable HE atoms must be expression
shaped.  This is a constructor/injectivity argument, not an appeal to either
executable matcher. -/
theorem bothExpressions_of_ne_nonvariable_solution
    {valuation : String → Metta.Atom} {left right : Atom}
    (hleft : DeclMatchSpec.Atom.isVarB left = false)
    (hright : DeclMatchSpec.Atom.isVarB right = false)
    (hequation : HEAtomEquationSatisfied valuation left right)
    (hne : left ≠ right) :
    BothExpressions left right := by
  cases left with
  | symbol leftName =>
      cases right with
      | symbol rightName =>
          have : leftName = rightName := by
            simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          exact (hne (congrArg Atom.symbol this)).elim
      | var rightName => simp [DeclMatchSpec.Atom.isVarB] at hright
      | grounded rightGround =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | expression rightAtoms =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
  | var leftName => simp [DeclMatchSpec.Atom.isVarB] at hleft
  | grounded leftGround =>
      cases right with
      | symbol rightName =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | var rightName => simp [DeclMatchSpec.Atom.isVarB] at hright
      | grounded rightGround =>
          have : leftGround = rightGround := by
            cases leftGround <;> cases rightGround <;>
              simp [HEAtomEquationSatisfied, toLeaTTaAtom,
                toLeaTTaGround, applyClassSolution] at hequation ⊢ <;>
              simp_all
          exact (hne (congrArg Atom.grounded this)).elim
      | expression rightAtoms =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
  | expression leftAtoms =>
      cases right with
      | symbol rightName =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | var rightName => simp [DeclMatchSpec.Atom.isVarB] at hright
      | grounded rightGround =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | expression rightAtoms => exact ⟨leftAtoms, rightAtoms, rfl, rfl⟩

private theorem humanVarNonVar_of_solution
    {valuation : String → Metta.Atom} {varName : String} {value : Atom}
    {bound : Nat}
    (hnonvar : HumanMatchMergeSpec.isVariableB value = false)
    (hequation : valuation varName =
      applyClassSolution valuation (toLeaTTaAtom value))
    (hvarBound : (valuation varName).size < bound)
    (hvalueBound : HESolutionAtomSize valuation value < bound) :
    ∃ out, HumanMatch (.var varName) value out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out ∧
      HEBindingSolutionSizeBound valuation out bound := by
  let out := Bindings.empty.assign varName value
  have hdeclNonvar : DeclMatchSpec.Atom.isVarB value = false := by
    cases value <;> simp_all [HumanMatchMergeSpec.isVariableB,
      DeclMatchSpec.Atom.isVarB]
  have hsatisfied : HEBindingSatisfied valuation out := by
    apply (hesat_assign_of_not_isBound
      (b := Bindings.empty) (v := varName) (val := value)
      (by simp [Bindings.isBound, Bindings.lookup, Bindings.empty])
      valuation).mpr
    exact ⟨hesat_empty valuation, hequation⟩
  have hnonvariable : HEAssignmentsNonVariable out :=
    assignmentsNonVariable_empty.assign hdeclNonvar
  have hadmissible : HumanMatchMergeSpec.SemanticLoopFree out :=
    semanticLoopFree_of_satisfied_nonvariable hsatisfied hnonvariable
  have hbound : HEBindingSolutionSizeBound valuation out bound :=
    (heBindingSolutionSizeBound_empty valuation bound).assign
      hvarBound hvalueBound
  exact ⟨out, .varNonVar hnonvar hadmissible,
    hsatisfied, hnonvariable, hbound⟩

private theorem humanNonVarVar_of_solution
    {valuation : String → Metta.Atom} {value : Atom} {varName : String}
    {bound : Nat}
    (hnonvar : HumanMatchMergeSpec.isVariableB value = false)
    (hequation : applyClassSolution valuation (toLeaTTaAtom value) =
      valuation varName)
    (hvalueBound : HESolutionAtomSize valuation value < bound)
    (hvarBound : (valuation varName).size < bound) :
    ∃ out, HumanMatch value (.var varName) out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out ∧
      HEBindingSolutionSizeBound valuation out bound := by
  let out := Bindings.empty.assign varName value
  have hdeclNonvar : DeclMatchSpec.Atom.isVarB value = false := by
    cases value <;> simp_all [HumanMatchMergeSpec.isVariableB,
      DeclMatchSpec.Atom.isVarB]
  have hsatisfied : HEBindingSatisfied valuation out := by
    apply (hesat_assign_of_not_isBound
      (b := Bindings.empty) (v := varName) (val := value)
      (by simp [Bindings.isBound, Bindings.lookup, Bindings.empty])
      valuation).mpr
    exact ⟨hesat_empty valuation, hequation.symm⟩
  have hnonvariable : HEAssignmentsNonVariable out :=
    assignmentsNonVariable_empty.assign hdeclNonvar
  have hadmissible : HumanMatchMergeSpec.SemanticLoopFree out :=
    semanticLoopFree_of_satisfied_nonvariable hsatisfied hnonvariable
  have hbound : HEBindingSolutionSizeBound valuation out bound :=
    (heBindingSolutionSizeBound_empty valuation bound).assign
      hvarBound hvalueBound
  exact ⟨out, .nonVarVar hnonvar hadmissible,
    hsatisfied, hnonvariable, hbound⟩

/-- Direct semantic completeness on the non-expression leaf fragment, with
the size and no-bare-variable invariants required by recursive merge-back. -/
theorem exists_humanMatch_leaf_of_solution
    {valuation : String → Metta.Atom} {left right : Atom} {bound : Nat}
    (hequation : HEAtomEquationSatisfied valuation left right)
    (hleaf : ¬BothExpressions left right)
    (hleftBound : HESolutionAtomSize valuation left < bound)
    (hrightBound : HESolutionAtomSize valuation right < bound) :
    ∃ out, HumanMatch left right out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out ∧
      HEBindingSolutionSizeBound valuation out bound := by
  cases left with
  | symbol leftName =>
      cases right with
      | symbol rightName =>
          have hname : leftName = rightName := by
            simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          subst rightName
          exact ⟨Bindings.empty,
            .symSym leftName HumanMatchMergeSpec.semanticLoopFree_empty,
            hesat_empty valuation, assignmentsNonVariable_empty,
            heBindingSolutionSizeBound_empty valuation bound⟩
      | var rightName =>
          exact humanNonVarVar_of_solution
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation)
            hleftBound (by simpa [HESolutionAtomSize] using hrightBound)
      | grounded rightGround =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | expression rightAtoms =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
  | var leftName =>
      cases right with
      | symbol rightName =>
          exact humanVarNonVar_of_solution
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation)
            (by simpa [HESolutionAtomSize] using hleftBound) hrightBound
      | var rightName =>
          let out := Bindings.empty.addEquality leftName rightName
          have hsatisfied : HEBindingSatisfied valuation out := by
            apply (hesat_addEquality valuation).mpr
            exact ⟨hesat_empty valuation, by
              simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
                applyClassSolution] using hequation⟩
          have hnonvariable : HEAssignmentsNonVariable out :=
            assignmentsNonVariable_empty.addEquality leftName rightName
          have hbound : HEBindingSolutionSizeBound valuation out bound :=
            (heBindingSolutionSizeBound_empty valuation bound).addEquality
              (by simpa [HESolutionAtomSize] using hleftBound)
              (by simpa [HESolutionAtomSize] using hrightBound)
          exact ⟨out, .varVar leftName rightName
              (semanticLoopFree_of_satisfied_nonvariable
                hsatisfied hnonvariable),
            hsatisfied, hnonvariable, hbound⟩
      | grounded rightGround =>
          exact humanVarNonVar_of_solution
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation)
            (by simpa [HESolutionAtomSize] using hleftBound) hrightBound
      | expression rightAtoms =>
          exact humanVarNonVar_of_solution
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation)
            (by simpa [HESolutionAtomSize] using hleftBound) hrightBound
  | grounded leftGround =>
      cases right with
      | symbol rightName =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | var rightName =>
          exact humanNonVarVar_of_solution
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation)
            hleftBound (by simpa [HESolutionAtomSize] using hrightBound)
      | grounded rightGround =>
          have hground : leftGround = rightGround := by
            cases leftGround <;> cases rightGround <;>
              simp [HEAtomEquationSatisfied, toLeaTTaAtom,
                toLeaTTaGround, applyClassSolution] at hequation ⊢ <;>
              simp_all
          subst rightGround
          exact ⟨Bindings.empty,
            .groundedLeftCustom
              (by simp [HumanMatchMergeSpec.isVariableB])
              (by simp [HumanMatchMergeSpec.equalityGroundedSemantic])
              ⟨rfl, rfl⟩ HumanMatchMergeSpec.semanticLoopFree_empty,
            hesat_empty valuation, assignmentsNonVariable_empty,
            heBindingSolutionSizeBound_empty valuation bound⟩
      | expression rightAtoms =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
  | expression leftAtoms =>
      cases right with
      | symbol rightName =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | var rightName =>
          exact humanNonVarVar_of_solution
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simpa [HEAtomEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation)
            hleftBound (by simpa [HESolutionAtomSize] using hrightBound)
      | grounded rightGround =>
          simp [HEAtomEquationSatisfied, toLeaTTaAtom,
            applyClassSolution] at hequation
      | expression rightAtoms =>
          exact (hleaf ⟨leftAtoms, rightAtoms, rfl, rfl⟩).elim

/-- Bounded semantic completeness of the human merge relation.  The right
record supplies the recursion ceiling; the live seed is already bounded at
that same ceiling. -/
def HumanSatisfiedMergeRelCompleteBelow
    (valuation : String → Metta.Atom) (bound : Nat) : Prop :=
  ∀ {ambientBound : Nat} {seed right : Bindings},
    bound ≤ ambientBound →
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEBindingSolutionSizeBound valuation seed ambientBound →
    HEBindingSatisfied valuation right →
    HEAssignmentsNonVariable right →
    HEBindingSolutionSizeBound valuation right bound →
    ∃ out,
      HumanMatchMergeSpec.MergeRel
        HumanMatchMergeSpec.equalityGroundedSemantic seed right out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out ∧
      HEBindingSolutionSizeBound valuation out ambientBound

/-- Simultaneous atom/list semantic completeness at a fixed semantic-size
ceiling, assuming merge completeness at that same ceiling. -/
private theorem humanBoundedMatcherPack
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HumanSatisfiedMergeRelCompleteBelow valuation bound) :
    (∀ {left right : Atom},
      HEAtomEquationSatisfied valuation left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, HumanMatch left right out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out bound) ∧
    (∀ {lefts rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      HESolutionAtomsSizeBound valuation lefts bound →
      HESolutionAtomsSizeBound valuation rights bound →
      ∃ out,
        HumanMatchMergeSpec.MatchListAccRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out bound) := by
  let AtomGoal : Atom → Prop := fun left =>
    ∀ {right : Atom},
      HEAtomEquationSatisfied valuation left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, HumanMatch left right out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out bound
  let ListGoal : List Atom → Prop := fun lefts =>
    ∀ {rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      HESolutionAtomsSizeBound valuation lefts bound →
      HESolutionAtomsSizeBound valuation rights bound →
      ∃ out,
        HumanMatchMergeSpec.MatchListAccRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out bound
  have hrec : ∀ left, AtomGoal left := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol right hequation hleft hright
      exact exists_humanMatch_leaf_of_solution hequation
        (by simp [BothExpressions]) hleft hright
    · intro name right hequation hleft hright
      exact exists_humanMatch_leaf_of_solution hequation
        (by simp [BothExpressions]) hleft hright
    · intro ground right hequation hleft hright
      exact exists_humanMatch_leaf_of_solution hequation
        (by simp [BothExpressions]) hleft hright
    · intro lefts hlefts right hequation hleft hright
      cases right with
      | symbol symbol =>
          exact exists_humanMatch_leaf_of_solution hequation
            (by simp [BothExpressions]) hleft hright
      | var name =>
          exact exists_humanMatch_leaf_of_solution hequation
            (by simp [BothExpressions]) hleft hright
      | grounded ground =>
          exact exists_humanMatch_leaf_of_solution hequation
            (by simp [BothExpressions]) hleft hright
      | expression rights =>
          have hlists : MettaAtomListsSatisfied valuation
              (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtom, applyClassSolution] using hequation
          obtain ⟨out, hitems, hsatisfied, hnonvariable, hbound⟩ :=
            hlefts (seed := Bindings.empty)
              (hesat_empty valuation) assignmentsNonVariable_empty
              (heBindingSolutionSizeBound_empty valuation bound)
              hlists
              (heSolutionAtomsSizeBound_of_expression_lt valuation hleft)
              (heSolutionAtomsSizeBound_of_expression_lt valuation hright)
          exact ⟨out, .expression hitems
              (semanticLoopFree_of_satisfied_nonvariable
                hsatisfied hnonvariable),
            hsatisfied, hnonvariable, hbound⟩
    · intro rights seed hseed hseedNonvariable hseedBound hlists
        hleftBound hrightBound
      cases rights with
      | nil => exact ⟨seed, .nil, hseed, hseedNonvariable, hseedBound⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
    · intro left lefts hleft hlefts rights seed hseed hseedNonvariable
        hseedBound hlists hleftBound hrightBound
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
              MettaAtomListsSatisfied valuation
                (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtoms] using hlists
          obtain ⟨matched, hmatched, hmatchedSatisfied,
              hmatchedNonvariable, hmatchedBound⟩ :=
            hleft hequations.1 hleftBound.head hrightBound.head
          obtain ⟨next, hnextMerge, hnextSatisfied,
              hnextNonvariable, hnextBound⟩ :=
            hmerge (ambientBound := bound) (Nat.le_refl bound)
              hseed hseedNonvariable hseedBound
              hmatchedSatisfied hmatchedNonvariable hmatchedBound
          obtain ⟨out, htail, houtSatisfied, houtNonvariable, houtBound⟩ :=
            hlefts hnextSatisfied hnextNonvariable hnextBound
              hequations.2 hleftBound.tail hrightBound.tail
          exact ⟨out, .cons hmatched hnextMerge htail,
            houtSatisfied, houtNonvariable, houtBound⟩
  refine ⟨?_, ?_⟩
  · intro left right hequation hleft hright
    exact hrec left hequation hleft hright
  · intro lefts rights seed hseed hseedNonvariable hseedBound hlists
      hleftBound hrightBound
    induction lefts generalizing rights seed with
    | nil =>
        cases rights with
        | nil => exact ⟨seed, .nil, hseed, hseedNonvariable, hseedBound⟩
        | cons right rights =>
            simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
    | cons left lefts ih =>
        cases rights with
        | nil =>
            simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
        | cons right rights =>
            have hequations :
                HEAtomEquationSatisfied valuation left right ∧
                MettaAtomListsSatisfied valuation
                  (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
              simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
                toLeaTTaAtoms] using hlists
            obtain ⟨matched, hmatched, hmatchedSatisfied,
                hmatchedNonvariable, hmatchedBound⟩ :=
              hrec left hequations.1 hleftBound.head hrightBound.head
            obtain ⟨next, hnextMerge, hnextSatisfied,
                hnextNonvariable, hnextBound⟩ :=
              hmerge (ambientBound := bound) (Nat.le_refl bound)
                hseed hseedNonvariable hseedBound
                hmatchedSatisfied hmatchedNonvariable hmatchedBound
            obtain ⟨out, htail, houtSatisfied, houtNonvariable, houtBound⟩ :=
              ih (rights := rights) (seed := next)
                hnextSatisfied hnextNonvariable hnextBound
                hequations.2 hleftBound.tail hrightBound.tail
            exact ⟨out, .cons hmatched hnextMerge htail,
              houtSatisfied, houtNonvariable, houtBound⟩

/-- Fold semantic value/equality insertion callbacks through the human
unordered constraint view.  All recursive matching is isolated in the two
callbacks; the fold itself is ordinary list induction. -/
private theorem humanMergeCompleteBelow_of_adds
    {valuation : String → Metta.Atom} {bound : Nat}
    (haddValue : ∀ {ambientBound : Nat} {seed : Bindings}
        {key : String} {value : Atom},
      bound ≤ ambientBound →
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed ambientBound →
      DeclMatchSpec.Atom.isVarB value = false →
      valuation key = applyClassSolution valuation (toLeaTTaAtom value) →
      (valuation key).size < bound →
      HESolutionAtomSize valuation value < bound →
      ∃ out,
        HumanMatchMergeSpec.AddVarBindingRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          seed key value out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out ambientBound)
    (haddEquality : ∀ {ambientBound : Nat} {seed : Bindings}
        {left right : String},
      bound ≤ ambientBound →
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed ambientBound →
      valuation left = valuation right →
      (valuation left).size < bound →
      (valuation right).size < bound →
      ∃ out,
        HumanMatchMergeSpec.AddVarEqualityRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          seed left right out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out ambientBound) :
    HumanSatisfiedMergeRelCompleteBelow valuation bound := by
  intro ambientBound seed right hboundAmbient
    hseed hseedNonvariable hseedBound
    hright hrightNonvariable hrightBound
  have foldConstraints : ∀
      (constraints : List HumanMatchMergeSpec.Constraint)
      (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      HEBindingSolutionSizeBound valuation before ambientBound →
      (∀ constraint ∈ constraints,
        HumanMatchSolutionTheory.ConstraintSatisfied valuation constraint) →
      (∀ key value,
        HumanMatchMergeSpec.Constraint.value key value ∈ constraints →
          DeclMatchSpec.Atom.isVarB value = false) →
      (∀ constraint ∈ constraints,
        match constraint with
        | .value key value =>
            (valuation key).size < bound ∧
              HESolutionAtomSize valuation value < bound
        | .equality left right =>
            (valuation left).size < bound ∧
              (valuation right).size < bound) →
      ∃ after,
        HumanMatchMergeSpec.MergeConstraintsRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          before constraints after ∧
        HEBindingSatisfied valuation after ∧
        HEAssignmentsNonVariable after ∧
        HEBindingSolutionSizeBound valuation after ambientBound := by
    intro constraints
    induction constraints with
    | nil =>
        intro before hbefore hbeforeNonvariable hbeforeBound _ _ _
        exact ⟨before, .nil, hbefore, hbeforeNonvariable, hbeforeBound⟩
    | cons constraint rest ih =>
        intro before hbefore hbeforeNonvariable hbeforeBound
          hsatisfied hnonvariable hbounds
        have hrestSatisfied : ∀ item ∈ rest,
            HumanMatchSolutionTheory.ConstraintSatisfied valuation item := by
          intro item hmem
          exact hsatisfied item (by simp [hmem])
        have hrestNonvariable : ∀ key value,
            HumanMatchMergeSpec.Constraint.value key value ∈ rest →
              DeclMatchSpec.Atom.isVarB value = false := by
          intro key value hmem
          exact hnonvariable key value (by simp [hmem])
        have hrestBounds : ∀ item ∈ rest,
            match item with
            | .value key value =>
                (valuation key).size < bound ∧
                  HESolutionAtomSize valuation value < bound
            | .equality left right =>
                (valuation left).size < bound ∧
                  (valuation right).size < bound := by
          intro item hmem
          exact hbounds item (by simp [hmem])
        cases constraint with
        | value key value =>
            obtain ⟨next, hadd, hnextSatisfied,
                hnextNonvariable, hnextBound⟩ :=
              haddValue hboundAmbient hbefore hbeforeNonvariable hbeforeBound
                (hnonvariable key value (by simp))
                (hsatisfied (.value key value) (by simp))
                (hbounds (.value key value) (by simp)).1
                (hbounds (.value key value) (by simp)).2
            obtain ⟨after, htail, hafterSatisfied,
                hafterNonvariable, hafterBound⟩ :=
              ih next hnextSatisfied hnextNonvariable hnextBound
                hrestSatisfied hrestNonvariable hrestBounds
            exact ⟨after, .value hadd htail,
              hafterSatisfied, hafterNonvariable, hafterBound⟩
        | equality left rightKey =>
            obtain ⟨next, hadd, hnextSatisfied,
                hnextNonvariable, hnextBound⟩ :=
              haddEquality hboundAmbient hbefore hbeforeNonvariable
                hbeforeBound
                (hsatisfied (.equality left rightKey) (by simp))
                (hbounds (.equality left rightKey) (by simp)).1
                (hbounds (.equality left rightKey) (by simp)).2
            obtain ⟨after, htail, hafterSatisfied,
                hafterNonvariable, hafterBound⟩ :=
              ih next hnextSatisfied hnextNonvariable hnextBound
                hrestSatisfied hrestNonvariable hrestBounds
            exact ⟨after, .equality hadd htail,
              hafterSatisfied, hafterNonvariable, hafterBound⟩
  have hconstraintsSatisfied : ∀ constraint ∈
      HumanMatchMergeSpec.constraints right,
      HumanMatchSolutionTheory.ConstraintSatisfied valuation constraint :=
    (HumanMatchSolutionTheory.constraintsSatisfied_constraints_iff
      valuation right).mpr hright
  have hconstraintsNonvariable : ∀ key value,
      HumanMatchMergeSpec.Constraint.value key value ∈
          HumanMatchMergeSpec.constraints right →
        DeclMatchSpec.Atom.isVarB value = false := by
    intro key value hmem
    exact hrightNonvariable.isVarB_eq_false_of_assignment
      (HumanMatchSolutionTheory.value_mem_constraints_iff.mp hmem)
  have hconstraintsBound : ∀ constraint ∈
      HumanMatchMergeSpec.constraints right,
      match constraint with
      | .value key value =>
          (valuation key).size < bound ∧
            HESolutionAtomSize valuation value < bound
      | .equality left rightKey =>
          (valuation left).size < bound ∧
            (valuation rightKey).size < bound := by
    intro constraint hmem
    cases constraint with
    | value key value =>
        exact hrightBound.1 key value
          (HumanMatchSolutionTheory.value_mem_constraints_iff.mp hmem)
    | equality left rightKey =>
        exact hrightBound.2 left rightKey
          (HumanMatchSolutionTheory.equality_mem_constraints_iff.mp hmem)
  obtain ⟨out, hfold, houtSatisfied, houtNonvariable, houtBound⟩ :=
    foldConstraints (HumanMatchMergeSpec.constraints right) seed
      hseed hseedNonvariable hseedBound hconstraintsSatisfied
      hconstraintsNonvariable hconstraintsBound
  exact ⟨out, .mk (List.Perm.refl _) hfold,
    houtSatisfied, houtNonvariable, houtBound⟩

/-- Expression-root semantic completeness at the exact root-size ceiling.
Immediate children are strictly smaller, so the fixed-ceiling matcher pack
applies to the pointwise list. -/
private theorem exists_humanExpressionMatch_at_solutionSize
    {valuation : String → Metta.Atom} {lefts rights : List Atom}
    {bound : Nat}
    (hmerge : HumanSatisfiedMergeRelCompleteBelow valuation bound)
    (hequation : HEAtomEquationSatisfied valuation
      (.expression lefts) (.expression rights))
    (hleftSize : HESolutionAtomSize valuation (.expression lefts) = bound)
    (hrightSize : HESolutionAtomSize valuation (.expression rights) = bound) :
    ∃ out, HumanMatch (.expression lefts) (.expression rights) out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out ∧
      HEBindingSolutionSizeBound valuation out bound := by
  have hlists : MettaAtomListsSatisfied valuation
      (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
    simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
      toLeaTTaAtom, applyClassSolution] using hequation
  have hleftBound : HESolutionAtomsSizeBound valuation lefts bound := by
    intro atom hmem
    rw [← hleftSize]
    exact heSolutionAtomSize_lt_expression_of_mem valuation hmem
  have hrightBound : HESolutionAtomsSizeBound valuation rights bound := by
    intro atom hmem
    rw [← hrightSize]
    exact heSolutionAtomSize_lt_expression_of_mem valuation hmem
  obtain ⟨out, hitems, hsatisfied, hnonvariable, hbound⟩ :=
    (humanBoundedMatcherPack hmerge).2
      (seed := Bindings.empty)
      (hesat_empty valuation) assignmentsNonVariable_empty
      (heBindingSolutionSizeBound_empty valuation bound)
      hlists hleftBound hrightBound
  exact ⟨out, .expression hitems
      (semanticLoopFree_of_satisfied_nonvariable hsatisfied hnonvariable),
    hsatisfied, hnonvariable, hbound⟩

/-- Equal scalar heads close immediately; every unequal co-satisfied
non-variable pair is expression-shaped and descends through its children. -/
private theorem exists_humanNonvariableMatch_at_solutionSize
    {valuation : String → Metta.Atom} {left right : Atom} {bound : Nat}
    (hmerge : HumanSatisfiedMergeRelCompleteBelow valuation bound)
    (hequation : HEAtomEquationSatisfied valuation left right)
    (hleftNonvariable : DeclMatchSpec.Atom.isVarB left = false)
    (hrightNonvariable : DeclMatchSpec.Atom.isVarB right = false)
    (hleftSize : HESolutionAtomSize valuation left = bound)
    (hrightSize : HESolutionAtomSize valuation right = bound) :
    ∃ out, HumanMatch left right out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out ∧
      HEBindingSolutionSizeBound valuation out bound := by
  by_cases hequal : left = right
  · subst right
    cases left with
    | symbol name =>
        exact ⟨Bindings.empty,
          .symSym name HumanMatchMergeSpec.semanticLoopFree_empty,
          hesat_empty valuation, assignmentsNonVariable_empty,
          heBindingSolutionSizeBound_empty valuation bound⟩
    | var name => simp [DeclMatchSpec.Atom.isVarB] at hleftNonvariable
    | grounded ground =>
        exact ⟨Bindings.empty,
          .groundedLeftCustom
            (by simp [HumanMatchMergeSpec.isVariableB])
            (by simp [HumanMatchMergeSpec.equalityGroundedSemantic])
            ⟨rfl, rfl⟩ HumanMatchMergeSpec.semanticLoopFree_empty,
          hesat_empty valuation, assignmentsNonVariable_empty,
          heBindingSolutionSizeBound_empty valuation bound⟩
    | expression atoms =>
        exact exists_humanExpressionMatch_at_solutionSize hmerge
          hequation hleftSize hrightSize
  · obtain ⟨lefts, rights, hleft, hright⟩ :=
      bothExpressions_of_ne_nonvariable_solution
        hleftNonvariable hrightNonvariable hequation hequal
    subst left
    subst right
    exact exists_humanExpressionMatch_at_solutionSize hmerge
      hequation hleftSize hrightSize

/-- Pointwise companion for class-wide reconciliation.  Every head is a
non-variable atom of the exact class-solution size; the live accumulator is
merged and remains bounded at that same ceiling. -/
private theorem exists_humanNonvariableMatchList_at_solutionSize
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HumanSatisfiedMergeRelCompleteBelow valuation bound) :
    ∀ {lefts rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      (∀ atom ∈ lefts,
        DeclMatchSpec.Atom.isVarB atom = false ∧
          HESolutionAtomSize valuation atom = bound) →
      (∀ atom ∈ rights,
        DeclMatchSpec.Atom.isVarB atom = false ∧
          HESolutionAtomSize valuation atom = bound) →
      ∃ out,
        HumanMatchMergeSpec.MatchListAccRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
        HEBindingSolutionSizeBound valuation out bound := by
  intro lefts
  induction lefts with
  | nil =>
      intro rights seed hseed hseedNonvariable hseedBound hlists _ _
      cases rights with
      | nil => exact ⟨seed, .nil, hseed, hseedNonvariable, hseedBound⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
  | cons left lefts ih =>
      intro rights seed hseed hseedNonvariable hseedBound hlists
        hleftData hrightData
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
              MettaAtomListsSatisfied valuation
                (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtoms] using hlists
          have hleftHead := hleftData left (by simp)
          have hrightHead := hrightData right (by simp)
          obtain ⟨matched, hmatched, hmatchedSatisfied,
              hmatchedNonvariable, hmatchedBound⟩ :=
            exists_humanNonvariableMatch_at_solutionSize hmerge
              hequations.1 hleftHead.1 hrightHead.1
              hleftHead.2 hrightHead.2
          obtain ⟨next, hnextMerge, hnextSatisfied,
              hnextNonvariable, hnextBound⟩ :=
            hmerge (ambientBound := bound) (Nat.le_refl bound)
              hseed hseedNonvariable hseedBound
              hmatchedSatisfied hmatchedNonvariable hmatchedBound
          have hleftTail : ∀ atom ∈ lefts,
              DeclMatchSpec.Atom.isVarB atom = false ∧
                HESolutionAtomSize valuation atom = bound := by
            intro atom hmem
            exact hleftData atom (by simp [hmem])
          have hrightTail : ∀ atom ∈ rights,
              DeclMatchSpec.Atom.isVarB atom = false ∧
                HESolutionAtomSize valuation atom = bound := by
            intro atom hmem
            exact hrightData atom (by simp [hmem])
          obtain ⟨out, htail, houtSatisfied,
              houtNonvariable, houtBound⟩ :=
            ih (rights := rights) (seed := next)
              hnextSatisfied hnextNonvariable hnextBound
              hequations.2 hleftTail hrightTail
          exact ⟨out, .cons hmatched hnextMerge htail,
            houtSatisfied, houtNonvariable, houtBound⟩

/-- Semantic completeness of the human merge relation.  Strong induction is
on the interpreted size of the right-hand record's values.  A genuine class
conflict at size `k` recursively matches only expression children and merges
their strictly-`k`-bounded result back into the ambient accumulator. -/
theorem humanSatisfiedMergeRelCompleteBelow
    (valuation : String → Metta.Atom) :
    ∀ bound, HumanSatisfiedMergeRelCompleteBelow valuation bound := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
      apply humanMergeCompleteBelow_of_adds
      · intro ambientBound seed key value hboundAmbient
          hseed hseedNonvariable hseedBound hvalueNonvariable hvalue
          hkeyBound hvalueBound
        cases hclass : seed.classValues key with
        | nil =>
            let out := seed.assign key value
            let hadd : HumanMatchMergeSpec.AddVarBindingRel
                HumanMatchMergeSpec.equalityGroundedSemantic
                seed key value out := .fresh hclass
            have houtSatisfied : HEBindingSatisfied valuation out := by
              apply (hesat_assign_of_not_isBound
                (isBound_eq_false_of_classValues_nil hclass) valuation).mpr
              exact ⟨hseed, hvalue⟩
            have houtNonvariable : HEAssignmentsNonVariable out :=
              hseedNonvariable.assign hvalueNonvariable
            have houtBound : HEBindingSolutionSizeBound
                valuation out ambientBound :=
              hseedBound.assign
                (hkeyBound.trans_le hboundAmbient)
                (hvalueBound.trans_le hboundAmbient)
            exact ⟨out, hadd, houtSatisfied,
              houtNonvariable, houtBound⟩
        | cons first rest =>
            have hvalues : (first :: rest).Perm (seed.classValues key) := by
              rw [hclass]
            by_cases hagree :
                HumanMatchMergeSpec.ValuesAgree (first :: rest)
            · by_cases hequal : value = first
              · let hadd : HumanMatchMergeSpec.AddVarBindingRel
                    HumanMatchMergeSpec.equalityGroundedSemantic
                    seed key value seed :=
                  .same hvalues hagree hequal
                exact ⟨seed, hadd, hseed,
                  hseedNonvariable, hseedBound⟩
              · have hfirstMem : first ∈ seed.classValues key := by
                  rw [hclass]
                  simp
                have hfirstEquation : HEAtomEquationSatisfied
                    valuation first value :=
                  (hseed.eq_applyClassSolution_of_mem_classValues
                    hfirstMem).symm.trans hvalue
                have hfirstSize : HESolutionAtomSize valuation first =
                    (valuation key).size :=
                  hseed.solutionAtomSize_classValue hfirstMem
                have hvalueSize : HESolutionAtomSize valuation value =
                    (valuation key).size :=
                  congrArg Metta.Atom.size hvalue.symm
                have hfirstNonvariable :
                    DeclMatchSpec.Atom.isVarB first = false :=
                  hseedNonvariable.isVarB_eq_false_of_classValue hfirstMem
                obtain ⟨lefts, rights, hfirstExpr, hvalueExpr⟩ :=
                  bothExpressions_of_ne_nonvariable_solution
                    hfirstNonvariable hvalueNonvariable
                    hfirstEquation (Ne.symm hequal)
                subst first
                subst value
                have hlocal : HumanSatisfiedMergeRelCompleteBelow
                    valuation (valuation key).size :=
                  ih _ hkeyBound
                obtain ⟨matched, hmatch, hmatchedSatisfied,
                    hmatchedNonvariable, hmatchedBound⟩ :=
                  exists_humanExpressionMatch_at_solutionSize hlocal
                    hfirstEquation hfirstSize hvalueSize
                have hlocalAmbient : (valuation key).size ≤ ambientBound :=
                  (Nat.le_of_lt hkeyBound).trans hboundAmbient
                obtain ⟨out, hmerge, houtSatisfied,
                    houtNonvariable, houtBound⟩ :=
                  hlocal (ambientBound := ambientBound) hlocalAmbient
                    hseed hseedNonvariable hseedBound
                    hmatchedSatisfied hmatchedNonvariable hmatchedBound
                let hadd : HumanMatchMergeSpec.AddVarBindingRel
                    HumanMatchMergeSpec.equalityGroundedSemantic
                    seed key (.expression rights) out :=
                  .conflict hvalues hagree hequal hmatch hmerge
                exact ⟨out, hadd, houtSatisfied,
                  houtNonvariable, houtBound⟩
            · have hfirstMem : first ∈ seed.classValues key := by
                rw [hclass]
                simp
              have hfirstSize : HESolutionAtomSize valuation first =
                  (valuation key).size :=
                hseed.solutionAtomSize_classValue hfirstMem
              have hvalueSize : HESolutionAtomSize valuation value =
                  (valuation key).size :=
                congrArg Metta.Atom.size hvalue.symm
              have hfirstNonvariable :
                  DeclMatchSpec.Atom.isVarB first = false :=
                hseedNonvariable.isVarB_eq_false_of_classValue hfirstMem
              have hlists := classValues_reconcileList_satisfied
                hseed hclass hvalue
              have hleftData : ∀ atom ∈
                  List.replicate (rest.length + 1) first,
                  DeclMatchSpec.Atom.isVarB atom = false ∧
                    HESolutionAtomSize valuation atom =
                      (valuation key).size := by
                intro atom hmem
                have hatom := List.eq_of_mem_replicate hmem
                subst atom
                exact ⟨hfirstNonvariable, hfirstSize⟩
              have hrightData : ∀ atom ∈ rest ++ [value],
                  DeclMatchSpec.Atom.isVarB atom = false ∧
                    HESolutionAtomSize valuation atom =
                      (valuation key).size := by
                intro atom hmem
                rcases List.mem_append.mp hmem with hrest | hlast
                · have hclassMem : atom ∈ seed.classValues key := by
                    rw [hclass]
                    exact List.mem_cons_of_mem first hrest
                  exact ⟨
                    hseedNonvariable.isVarB_eq_false_of_classValue hclassMem,
                    hseed.solutionAtomSize_classValue hclassMem⟩
                · simp only [List.mem_singleton] at hlast
                  subst atom
                  exact ⟨hvalueNonvariable, hvalueSize⟩
              have hlocal : HumanSatisfiedMergeRelCompleteBelow
                  valuation (valuation key).size :=
                ih _ hkeyBound
              obtain ⟨matched, hlist, hmatchedSatisfied,
                  hmatchedNonvariable, hmatchedBound⟩ :=
                exists_humanNonvariableMatchList_at_solutionSize hlocal
                  (seed := Bindings.empty)
                  (hesat_empty valuation) assignmentsNonVariable_empty
                  (heBindingSolutionSizeBound_empty valuation
                    (valuation key).size)
                  hlists hleftData hrightData
              have hlocalAmbient : (valuation key).size ≤ ambientBound :=
                (Nat.le_of_lt hkeyBound).trans hboundAmbient
              obtain ⟨out, hmerge, houtSatisfied,
                  houtNonvariable, houtBound⟩ :=
                hlocal (ambientBound := ambientBound) hlocalAmbient
                  hseed hseedNonvariable hseedBound
                  hmatchedSatisfied hmatchedNonvariable hmatchedBound
              let hadd : HumanMatchMergeSpec.AddVarBindingRel
                  HumanMatchMergeSpec.equalityGroundedSemantic
                  seed key value out :=
                .reconcile hvalues hagree hlist hmerge
              exact ⟨out, hadd, houtSatisfied,
                houtNonvariable, houtBound⟩
      · intro ambientBound seed left right hboundAmbient
          hseed hseedNonvariable hseedBound hequality
          hleftBound hrightBound
        let candidate := seed.addEquality left right
        have hcandidateSatisfied : HEBindingSatisfied valuation candidate :=
          (hesat_addEquality valuation).mpr ⟨hseed, hequality⟩
        have hcandidateNonvariable : HEAssignmentsNonVariable candidate :=
          hseedNonvariable.addEquality left right
        have hcandidateBound : HEBindingSolutionSizeBound
            valuation candidate ambientBound :=
          hseedBound.addEquality
            (hleftBound.trans_le hboundAmbient)
            (hrightBound.trans_le hboundAmbient)
        cases hclass : candidate.classValues left with
        | nil =>
            let hadd : HumanMatchMergeSpec.AddVarEqualityRel
                HumanMatchMergeSpec.equalityGroundedSemantic
                seed left right candidate :=
              .consistent hclass (by simp [HumanMatchMergeSpec.ValuesAgree])
            exact ⟨candidate, hadd, hcandidateSatisfied,
              hcandidateNonvariable, hcandidateBound⟩
        | cons first rest =>
            have hvalues : (first :: rest).Perm
                ((seed.addEquality left right).classValues left) := by
              simpa only [candidate] using (show
                (first :: rest).Perm (candidate.classValues left) by
                  rw [hclass])
            by_cases hagree :
                HumanMatchMergeSpec.ValuesAgree (first :: rest)
            · let hadd : HumanMatchMergeSpec.AddVarEqualityRel
                  HumanMatchMergeSpec.equalityGroundedSemantic
                  seed left right candidate :=
                .consistent (by simpa only [candidate] using hclass) hagree
              exact ⟨candidate, hadd, hcandidateSatisfied,
                hcandidateNonvariable, hcandidateBound⟩
            · have hfirstMem : first ∈ candidate.classValues left := by
                rw [hclass]
                simp
              have hfirstSize : HESolutionAtomSize valuation first =
                  (valuation left).size :=
                hcandidateSatisfied.solutionAtomSize_classValue hfirstMem
              have hfirstNonvariable :
                  DeclMatchSpec.Atom.isVarB first = false :=
                hcandidateNonvariable.isVarB_eq_false_of_classValue hfirstMem
              have hlists := classValues_replicateTail_satisfied
                hcandidateSatisfied hclass
              have hleftData : ∀ atom ∈ List.replicate rest.length first,
                  DeclMatchSpec.Atom.isVarB atom = false ∧
                    HESolutionAtomSize valuation atom =
                      (valuation left).size := by
                intro atom hmem
                have hatom := List.eq_of_mem_replicate hmem
                subst atom
                exact ⟨hfirstNonvariable, hfirstSize⟩
              have hrightData : ∀ atom ∈ rest,
                  DeclMatchSpec.Atom.isVarB atom = false ∧
                    HESolutionAtomSize valuation atom =
                      (valuation left).size := by
                intro atom hmem
                have hclassMem : atom ∈ candidate.classValues left := by
                  rw [hclass]
                  exact List.mem_cons_of_mem first hmem
                exact ⟨
                  hcandidateNonvariable.isVarB_eq_false_of_classValue
                    hclassMem,
                  hcandidateSatisfied.solutionAtomSize_classValue hclassMem⟩
              have hlocal : HumanSatisfiedMergeRelCompleteBelow
                  valuation (valuation left).size :=
                ih _ hleftBound
              obtain ⟨matched, hlist, hmatchedSatisfied,
                  hmatchedNonvariable, hmatchedBound⟩ :=
                exists_humanNonvariableMatchList_at_solutionSize hlocal
                  (seed := Bindings.empty)
                  (hesat_empty valuation) assignmentsNonVariable_empty
                  (heBindingSolutionSizeBound_empty valuation
                    (valuation left).size)
                  hlists hleftData hrightData
              have hlocalAmbient : (valuation left).size ≤ ambientBound :=
                (Nat.le_of_lt hleftBound).trans hboundAmbient
              obtain ⟨out, hmerge, houtSatisfied,
                  houtNonvariable, houtBound⟩ :=
                hlocal (ambientBound := ambientBound) hlocalAmbient
                  hcandidateSatisfied hcandidateNonvariable hcandidateBound
                  hmatchedSatisfied hmatchedNonvariable hmatchedBound
              let hadd : HumanMatchMergeSpec.AddVarEqualityRel
                  HumanMatchMergeSpec.equalityGroundedSemantic
                  seed left right out :=
                .reconcile hvalues hagree hlist hmerge
              exact ⟨out, hadd, houtSatisfied,
                houtNonvariable, houtBound⟩

/-- Every semantically satisfiable human atom equation has a human matcher
derivation.  This is the assumption-free semantic completeness theorem for
the executable-independent relation. -/
theorem exists_humanMatch_of_solution
    {valuation : String → Metta.Atom} {left right : Atom}
    (hequation : HEAtomEquationSatisfied valuation left right) :
    ∃ out, HumanMatch left right out ∧
      HEBindingSatisfied valuation out := by
  let bound := max
    (HESolutionAtomSize valuation left)
    (HESolutionAtomSize valuation right) + 1
  have hleftBound : HESolutionAtomSize valuation left < bound :=
    (Nat.le_max_left _ _).trans_lt (Nat.lt_succ_self _)
  have hrightBound : HESolutionAtomSize valuation right < bound :=
    (Nat.le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  obtain ⟨out, hmatch, hsatisfied, _hnonvariable, _hbound⟩ :=
    (humanBoundedMatcherPack
      (humanSatisfiedMergeRelCompleteBelow valuation bound)).1
      hequation hleftBound hrightBound
  exact ⟨out, hmatch, hsatisfied⟩

/-- Every finite human binding record has a strict semantic-size ceiling at
any fixed valuation. -/
theorem exists_humanBindingSolutionSizeBound
    (valuation : String → Metta.Atom) (bindings : Bindings) :
    ∃ bound, HEBindingSolutionSizeBound valuation bindings bound := by
  let atoms :=
    bindings.assignments.flatMap
        (fun relation => [.var relation.1, relation.2]) ++
      bindings.equalities.flatMap
        (fun relation => [.var relation.1, .var relation.2])
  obtain ⟨bound, hbound⟩ :=
    exists_heSolutionAtomsSizeBound valuation atoms
  refine ⟨bound, ?_, ?_⟩
  · intro key value hmem
    constructor
    · simpa [heSolutionAtomSize_var] using
        hbound (.var key) (by
          apply List.mem_append_left
          exact List.mem_flatMap.mpr
            ⟨(key, value), hmem, by simp⟩)
    · exact hbound value (by
        apply List.mem_append_left
        exact List.mem_flatMap.mpr
          ⟨(key, value), hmem, by simp⟩)
  · intro left right hmem
    constructor
    · simpa [heSolutionAtomSize_var] using
        hbound (.var left) (by
          apply List.mem_append_right
          exact List.mem_flatMap.mpr
            ⟨(left, right), hmem, by simp⟩)
    · simpa [heSolutionAtomSize_var] using
        hbound (.var right) (by
          apply List.mem_append_right
          exact List.mem_flatMap.mpr
            ⟨(left, right), hmem, by simp⟩)

/-- Any two non-variable human binding records with a common solution have a
declarative human merge.  This is the unbounded public projection of the
semantic-size construction. -/
theorem exists_humanMerge_of_solution
    {valuation : String → Metta.Atom} {left right : Bindings}
    (hleft : HEBindingSatisfied valuation left)
    (hleftNonvariable : HEAssignmentsNonVariable left)
    (hright : HEBindingSatisfied valuation right)
    (hrightNonvariable : HEAssignmentsNonVariable right) :
    ∃ out,
      HumanMatchMergeSpec.MergeRel
        HumanMatchMergeSpec.equalityGroundedSemantic left right out ∧
      HEBindingSatisfied valuation out ∧
      HEAssignmentsNonVariable out := by
  obtain ⟨leftBound, hleftBound⟩ :=
    exists_humanBindingSolutionSizeBound valuation left
  obtain ⟨rightBound, hrightBound⟩ :=
    exists_humanBindingSolutionSizeBound valuation right
  let bound := max leftBound rightBound
  obtain ⟨out, hmerge, houtSatisfied, houtNonvariable, _houtBound⟩ :=
    humanSatisfiedMergeRelCompleteBelow valuation bound
      (ambientBound := bound) (Nat.le_refl bound)
      hleft hleftNonvariable
      (hleftBound.mono (Nat.le_max_left _ _))
      hright hrightNonvariable
      (hrightBound.mono (Nat.le_max_right _ _))
  exact ⟨out, hmerge, houtSatisfied, houtNonvariable⟩

/-- Positive recursive canary: one valuation witnessing two equal expression
images yields a human match without passing through an executable matcher. -/
example : ∃ out, HumanMatch
    (.expression [.var "x", .symbol "a"])
    (.expression [.symbol "b", .var "y"]) out := by
  let valuation : String → Metta.Atom := fun name =>
    if name = "x" then .sym "b" else .sym "a"
  obtain ⟨out, hmatch, _⟩ := exists_humanMatch_of_solution
    (valuation := valuation)
    (left := .expression [.var "x", .symbol "a"])
    (right := .expression [.symbol "b", .var "y"])
    (by simp [HEAtomEquationSatisfied, valuation, toLeaTTaAtom,
      applyClassSolution])
  exact ⟨out, hmatch⟩

/-- Negative semantic canary: distinct symbols have no common valuation, so
semantic completeness correctly has no premise from which to construct a
derivation. -/
example : ¬∃ valuation : String → Metta.Atom,
    HEAtomEquationSatisfied valuation (.symbol "a") (.symbol "b") := by
  intro h
  rcases h with ⟨valuation, hequation⟩
  simp [HEAtomEquationSatisfied, toLeaTTaAtom,
    applyClassSolution] at hequation

end Mettapedia.Languages.MeTTa.HE.HumanMatchCompleteness
