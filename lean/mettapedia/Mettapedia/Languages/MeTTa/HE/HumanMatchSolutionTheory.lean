import Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec
import Mettapedia.Languages.MeTTa.HE.MatchSolutionTheory

/-!
# Solution theory of the human-grounded match/merge relation

This file proves the observation law for the executable-independent human
specification.  A match presents exactly its input atom equation; a merge
presents exactly the conjunction of its input binding theories.  Thus relation
order, equality-edge orientation, representative chronology, and the selected
reconciliation derivation are absent from the formal observation.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanMatchSolutionTheory

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Satisfaction of one neutral human binding constraint. -/
def ConstraintSatisfied
    (valuation : String → Metta.Atom) : HumanMatchMergeSpec.Constraint → Prop
  | .value varName value =>
      valuation varName =
        applyClassSolution valuation (toLeaTTaAtom value)
  | .equality left right => valuation left = valuation right

/-- Satisfaction of every constraint in a concrete fold ordering. -/
def ConstraintsSatisfied
    (valuation : String → Metta.Atom)
    (constraints : List HumanMatchMergeSpec.Constraint) : Prop :=
  ∀ constraint ∈ constraints, ConstraintSatisfied valuation constraint

@[simp] theorem value_mem_constraints_iff
    {bindings : Bindings} {varName : String} {value : Atom} :
    HumanMatchMergeSpec.Constraint.value varName value ∈
        HumanMatchMergeSpec.constraints bindings ↔
      (varName, value) ∈ bindings.assignments := by
  simp [HumanMatchMergeSpec.constraints]

@[simp] theorem equality_mem_constraints_iff
    {bindings : Bindings} {left right : String} :
    HumanMatchMergeSpec.Constraint.equality left right ∈
        HumanMatchMergeSpec.constraints bindings ↔
      (left, right) ∈ bindings.equalities := by
  simp [HumanMatchMergeSpec.constraints]

/-- The neutral constraint view presents exactly `HEBindingSatisfied`. -/
theorem constraintsSatisfied_constraints_iff
    (valuation : String → Metta.Atom) (bindings : Bindings) :
    ConstraintsSatisfied valuation
        (HumanMatchMergeSpec.constraints bindings) ↔
      HEBindingSatisfied valuation bindings := by
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · intro varName value hmem
      exact hall (.value varName value)
        (value_mem_constraints_iff.mpr hmem)
    · intro left right hmem
      exact hall (.equality left right)
        (equality_mem_constraints_iff.mpr hmem)
  · rintro ⟨hvalues, hequalities⟩ constraint hmem
    cases constraint with
    | value varName value =>
        exact hvalues varName value
          (value_mem_constraints_iff.mp hmem)
    | equality left right =>
        exact hequalities left right
          (equality_mem_constraints_iff.mp hmem)

theorem constraintsSatisfied_iff_of_perm
    {valuation : String → Metta.Atom}
    {left right : List HumanMatchMergeSpec.Constraint}
    (hperm : left.Perm right) :
    ConstraintsSatisfied valuation left ↔
      ConstraintsSatisfied valuation right := by
  constructor
  · intro hall constraint hmem
    exact hall constraint ((List.Perm.mem_iff hperm).mpr hmem)
  · intro hall constraint hmem
    exact hall constraint ((List.Perm.mem_iff hperm).mp hmem)

/-! ## Simultaneous observation theorem -/

/-- The full six-relation mutual induction.  The public corollaries below
project its matcher and merge legs. -/
private theorem solutionPack
    {left right : Atom} {bindings : Bindings}
    (derivation : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      left right bindings) :
    ∀ valuation : String → Metta.Atom,
      (HEBindingSatisfied valuation bindings ↔
        applyClassSolution valuation (toLeaTTaAtom left) =
          applyClassSolution valuation (toLeaTTaAtom right)) := by
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun left right bindings _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation bindings ↔
          applyClassSolution valuation (toLeaTTaAtom left) =
            applyClassSolution valuation (toLeaTTaAtom right)))
    (motive_2 := fun left right seed out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            (toLeaTTaAtoms left).map (applyClassSolution valuation) =
              (toLeaTTaAtoms right).map
                (applyClassSolution valuation)))
    (motive_3 := fun bindings varName value out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation varName =
              applyClassSolution valuation (toLeaTTaAtom value)))
    (motive_4 := fun bindings left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation left = valuation right))
    (motive_5 := fun seed constraints out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            ConstraintsSatisfied valuation constraints))
    (motive_6 := fun left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation left ∧
            HEBindingSatisfied valuation right))
    (t := derivation)
  next =>
      intro symbol hadmissible valuation
      simp
  next =>
      intro left right hadmissible valuation
      rw [hesat_addEquality]
      simp
  next =>
      intro varName value hnonvar hadmissible valuation
      rw [hesat_assign_of_not_isBound (by
        simp [Bindings.isBound, Bindings.lookup, Bindings.empty])]
      simp
  next =>
      intro value varName hnonvar hadmissible valuation
      rw [hesat_assign_of_not_isBound (by
        simp [Bindings.isBound, Bindings.lookup, Bindings.empty])]
      simp [eq_comm]
  next =>
      intro left right out hitems hadmissible ih valuation
      rw [ih valuation]
      simp [applyToLea_expression]
  next =>
      intro grounded right out hright hcustom hmatch hadmissible
      rcases hmatch with ⟨hrightEq, hout⟩
      subst right
      subst out
      intro valuation
      simp
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hmatch hadmissible
      rcases hmatch with ⟨hleftEq, hout⟩
      subst left
      subst out
      intro valuation
      simp
  next =>
      intro left right hleft hright hadmissible
      exact (hleft (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim
  next =>
      intro seed valuation
      simp
  next =>
      intro left right lefts rights seed matched next out
        hmatch hmerge htail ihMatch ihMerge ihTail valuation
      rw [ihTail valuation, ihMerge valuation, ihMatch valuation]
      simp only [toLeaTTaAtoms_cons, List.map_cons, List.cons.injEq]
      tauto
  next =>
      intro bindings varName value hvalues valuation
      exact hesat_assign_of_not_isBound
        (isBound_eq_false_of_classValues_nil hvalues) valuation
  next =>
      intro bindings varName value first rest hvalues hagree hvalue
      subst value
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      constructor
      · intro hsat
        exact ⟨hsat,
          hsat.eq_applyClassSolution_of_mem_classValues hfirst⟩
      · exact fun hsat => hsat.1
  next =>
      intro bindings varName value first rest matched out hvalues hagree
        hne hmatch hmerge ihMatch ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihMatch valuation]
      have hvalue : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat =>
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
      constructor
      · rintro ⟨hsat, hmatched⟩
        exact ⟨hsat, (hvalue hsat).trans hmatched⟩
      · rintro ⟨hsat, hnew⟩
        exact ⟨hsat, (hvalue hsat).symm.trans hnew⟩
  next =>
      intro bindings varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [show rest.length + 1 = (rest ++ [value]).length by simp]
      rw [replicate_eq_map_iff valuation first (rest ++ [value])]
      have hhead : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat =>
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
      have hrest : HEBindingSatisfied valuation bindings →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hclass : atom ∈ bindings.classValues varName :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            (hhead hsat)
      constructor
      · rintro ⟨hsat, hall⟩
        have hnew := hall value (List.mem_append_right rest (by simp))
        exact ⟨hsat, (hhead hsat).trans hnew.symm⟩
      · rintro ⟨hsat, hnew⟩
        refine ⟨hsat, fun atom hatom => ?_⟩
        rcases List.mem_append.mp hatom with hatom | hatom
        · exact hrest hsat atom hatom
        · simp only [List.mem_singleton] at hatom
          subst atom
          exact ((hhead hsat).symm.trans hnew).symm
  next =>
      intro bindings left right values hvalues hagree valuation
      exact hesat_addEquality valuation
  next =>
      intro bindings left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈
          (bindings.addEquality left right).classValues left :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation, hesat_addEquality]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [replicate_eq_map_iff valuation first rest]
      have hall : HEBindingSatisfied valuation
            (bindings.addEquality left right) →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hheadSat :=
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
        have hclass : atom ∈
            (bindings.addEquality left right).classValues left :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            hheadSat
      constructor
      · rintro ⟨hsat, hallMatched⟩
        exact hsat
      · intro hsat
        have hcandidate := (hesat_addEquality valuation).mpr hsat
        exact ⟨hsat, hall hcandidate⟩
  next =>
      intro seed valuation
      simp [ConstraintsSatisfied]
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro left right out order hperm hfold ihFold valuation
      rw [ihFold valuation,
        constraintsSatisfied_iff_of_perm hperm,
        constraintsSatisfied_constraints_iff]

/-- Human matching presents exactly the equation between its input atoms. -/
theorem matchRel_solution_iff
    {left right : Atom} {bindings : Bindings}
    (derivation : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      left right bindings)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation bindings ↔
      applyClassSolution valuation (toLeaTTaAtom left) =
        applyClassSolution valuation (toLeaTTaAtom right) :=
  solutionPack derivation valuation

/-- Human merging presents exactly the conjunction of its two input binding
theories.  This is the standalone merge-root projection of the same mutual
observation invariant used by `matchRel_solution_iff`. -/
theorem mergeRel_solution_iff
    {left right out : Bindings}
    (derivation : HumanMatchMergeSpec.MergeRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right out)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation left ∧
        HEBindingSatisfied valuation right := by
  apply HumanMatchMergeSpec.MergeRel.rec
    (motive_1 := fun left right bindings _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation bindings ↔
          applyClassSolution valuation (toLeaTTaAtom left) =
            applyClassSolution valuation (toLeaTTaAtom right)))
    (motive_2 := fun left right seed out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            (toLeaTTaAtoms left).map (applyClassSolution valuation) =
              (toLeaTTaAtoms right).map
                (applyClassSolution valuation)))
    (motive_3 := fun bindings varName value out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation varName =
              applyClassSolution valuation (toLeaTTaAtom value)))
    (motive_4 := fun bindings left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation bindings ∧
            valuation left = valuation right))
    (motive_5 := fun seed constraints out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            ConstraintsSatisfied valuation constraints))
    (motive_6 := fun left right out _ =>
      ∀ valuation : String → Metta.Atom,
        (HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation left ∧
            HEBindingSatisfied valuation right))
    (t := derivation)
  next =>
      intro symbol hadmissible
      exact matchRel_solution_iff (.symSym symbol hadmissible)
  next =>
      intro left right hadmissible
      exact matchRel_solution_iff (.varVar left right hadmissible)
  next =>
      intro varName value hnonvar hadmissible
      exact matchRel_solution_iff (.varNonVar hnonvar hadmissible)
  next =>
      intro value varName hnonvar hadmissible
      exact matchRel_solution_iff (.nonVarVar hnonvar hadmissible)
  next =>
      intro left right out hitems hadmissible ih
      exact matchRel_solution_iff (.expression hitems hadmissible)
  next =>
      intro grounded right out hright hcustom hmatch hadmissible
      exact matchRel_solution_iff
        (.groundedLeftCustom hright hcustom hmatch hadmissible)
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hmatch hadmissible
      exact matchRel_solution_iff
        (.groundedRightCustom hleft hleftNoCustom hcustom hmatch hadmissible)
  next =>
      intro left right hleft hright hadmissible
      exact matchRel_solution_iff
        (.groundedFallback hleft hright hadmissible)
  next =>
      intro seed valuation
      simp
  next =>
      intro left right lefts rights seed matched next out
        hmatch hmerge htail ihMatch ihMerge ihTail valuation
      rw [ihTail valuation, ihMerge valuation, ihMatch valuation]
      simp only [toLeaTTaAtoms_cons, List.map_cons, List.cons.injEq]
      tauto
  next =>
      intro bindings varName value hvalues valuation
      exact hesat_assign_of_not_isBound
        (isBound_eq_false_of_classValues_nil hvalues) valuation
  next =>
      intro bindings varName value first rest hvalues hagree hvalue
      subst value
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      constructor
      · intro hsat
        exact ⟨hsat,
          hsat.eq_applyClassSolution_of_mem_classValues hfirst⟩
      · exact fun hsat => hsat.1
  next =>
      intro bindings varName value first rest matched out hvalues hagree
        hne hmatch hmerge ihMatch ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihMatch valuation]
      have hvalue : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat => hsat.eq_applyClassSolution_of_mem_classValues hfirst
      constructor
      · rintro ⟨hsat, hmatched⟩
        exact ⟨hsat, (hvalue hsat).trans hmatched⟩
      · rintro ⟨hsat, hnew⟩
        exact ⟨hsat, (hvalue hsat).symm.trans hnew⟩
  next =>
      intro bindings varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈ bindings.classValues varName :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [show rest.length + 1 = (rest ++ [value]).length by simp]
      rw [replicate_eq_map_iff valuation first (rest ++ [value])]
      have hhead : HEBindingSatisfied valuation bindings →
          valuation varName =
            applyClassSolution valuation (toLeaTTaAtom first) :=
        fun hsat => hsat.eq_applyClassSolution_of_mem_classValues hfirst
      have hrest : HEBindingSatisfied valuation bindings →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hclass : atom ∈ bindings.classValues varName :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            (hhead hsat)
      constructor
      · rintro ⟨hsat, hall⟩
        have hnew := hall value (List.mem_append_right rest (by simp))
        exact ⟨hsat, (hhead hsat).trans hnew.symm⟩
      · rintro ⟨hsat, hnew⟩
        refine ⟨hsat, fun atom hatom => ?_⟩
        rcases List.mem_append.mp hatom with hatom | hatom
        · exact hrest hsat atom hatom
        · simp only [List.mem_singleton] at hatom
          subst atom
          exact ((hhead hsat).symm.trans hnew).symm
  next =>
      intro bindings left right values hvalues hagree valuation
      exact hesat_addEquality valuation
  next =>
      intro bindings left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      have hfirst : first ∈
          (bindings.addEquality left right).classValues left :=
        (List.Perm.mem_iff hvalues).mp (by simp)
      intro valuation
      rw [ihMerge valuation, ihList valuation, hesat_addEquality]
      simp only [hesat_empty_iff, true_and,
        solutionTheory_toLeaTTaAtoms_eq_map, List.map_map,
        List.map_replicate]
      rw [replicate_eq_map_iff valuation first rest]
      have hall : HEBindingSatisfied valuation
            (bindings.addEquality left right) →
          ∀ atom ∈ rest,
            applyClassSolution valuation (toLeaTTaAtom atom) =
              applyClassSolution valuation (toLeaTTaAtom first) := by
        intro hsat atom hatom
        have hheadSat :=
          hsat.eq_applyClassSolution_of_mem_classValues hfirst
        have hclass : atom ∈
            (bindings.addEquality left right).classValues left :=
          (List.Perm.mem_iff hvalues).mp (by simp [hatom])
        exact
          (hsat.eq_applyClassSolution_of_mem_classValues hclass).symm.trans
            hheadSat
      constructor
      · rintro ⟨hsat, hallMatched⟩
        exact hsat
      · intro hsat
        have hcandidate := (hesat_addEquality valuation).mpr hsat
        exact ⟨hsat, hall hcandidate⟩
  next =>
      intro seed valuation
      simp [ConstraintsSatisfied]
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail valuation
      rw [ihTail valuation, ihAdd valuation]
      simp [ConstraintsSatisfied, ConstraintSatisfied, and_assoc]
  next =>
      intro left right out order hperm hfold ihFold valuation
      rw [ihFold valuation,
        constraintsSatisfied_iff_of_perm hperm,
        constraintsSatisfied_constraints_iff]

/-- Pointwise human list matching presents the live seed theory together with
the pointwise equations.  This projection is useful when a recursive class
reconciliation consumes its transient match record during merge-back. -/
theorem matchListAccRel_solution_iff
    {left right : List Atom} {seed out : Bindings}
    (derivation : HumanMatchMergeSpec.MatchListAccRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right seed out)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation seed ∧
        (toLeaTTaAtoms left).map (applyClassSolution valuation) =
          (toLeaTTaAtoms right).map (applyClassSolution valuation) := by
  apply HumanMatchMergeSpec.MatchListAccRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun left right seed out _ =>
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation seed ∧
          (toLeaTTaAtoms left).map (applyClassSolution valuation) =
            (toLeaTTaAtoms right).map (applyClassSolution valuation))
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (t := derivation)
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => simp
  next =>
      intro headLeft headRight tailLeft tailRight live matched next out
        hhead hmerge htail ihHead ihMerge ihTail
      rw [ihTail, mergeRel_solution_iff hmerge valuation,
        matchRel_solution_iff hhead valuation]
      simp only [toLeaTTaAtoms, List.map_cons, List.cons.injEq]
      aesop
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial

/-- Any two human-spec derivations of the same match have the same complete
binding solution theory.  In particular, constraint order, equality-edge
orientation, representative chronology, and reconciliation path cannot be
observed through binding satisfaction. -/
theorem matchRel_solutionTheory_unique
    {left right : Atom} {first second : Bindings}
    (hfirst : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right first)
    (hsecond : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right second) :
    ∀ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation first ↔
        HEBindingSatisfied valuation second := by
  intro valuation
  exact (matchRel_solution_iff hfirst valuation).trans
    (matchRel_solution_iff hsecond valuation).symm

/-- A human-spec match result and any repaired-LeaTTa result for the translated
equation present the same complete binding solution theory.  This theorem is
direct: it compares the human relation with LeaTTa and has no HE executable
matcher or merger premise. -/
theorem humanMatch_leaMatch_solutionTheoryEquiv
    {query pattern : Atom} {humanOut : Bindings}
    {leaOut : Metta.Bindings}
    (hhuman : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      query pattern humanOut)
    (hlea : leaOut ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query)) :
    LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  intro valuation
  rw [matchRel_solution_iff hhuman valuation,
    leaMatchAtoms_solution_iff valuation
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hlea]
  simp only [MettaEquationSatisfied]
  exact eq_comm

end Mettapedia.Languages.MeTTa.HE.HumanMatchSolutionTheory
