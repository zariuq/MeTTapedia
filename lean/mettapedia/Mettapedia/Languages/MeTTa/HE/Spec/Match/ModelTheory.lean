import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
import Mathlib.Order.WellFoundedSet

/-!
# Model theory for the executable-independent spec matcher

This file develops the finite dependency order used to construct models of
admitted spec matcher derivations.  The order is semantic: one equality class
precedes another exactly when a stored compound value depends on it.  Concrete
binding-list order, equality-edge orientation, representative chronology, and
unification fuel do not occur in the construction.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Match.ModelTheory

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Finite support -/

/-- Variables occurring as assignment keys, inside assignment values, or as
equality endpoints in a spec binding record. -/
def bindingSupport (bindings : Bindings) : Finset String :=
  (bindings.assignments.flatMap (fun entry =>
      entry.1 :: (toLeaTTaAtom entry.2).vars) ++
    bindings.equalities.flatMap (fun edge => [edge.1, edge.2])).toFinset

private theorem mem_toLeaTTaAtoms_of_mem {atoms : List Atom} {atom : Atom}
    (hmem : atom ∈ atoms) :
    toLeaTTaAtom atom ∈ toLeaTTaAtoms atoms := by
  induction atoms with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [toLeaTTaAtoms, List.mem_cons] at hmem ⊢
      exact hmem.elim (fun heq => Or.inl (congrArg toLeaTTaAtom heq))
        (fun htail => Or.inr (ih htail))

/-- The neutral occurrence relation has exactly the variable support of the
structural translation. -/
theorem atomOccurs_iff_mem_translated_vars {atom : Atom} {name : String} :
    Spec.Match.Merge.AtomOccurs atom name ↔
      name ∈ (toLeaTTaAtom atom).vars := by
  constructor
  · intro hoccurs
    induction hoccurs with
    | var => simp [toLeaTTaAtom, Metta.Atom.vars]
    | @expression atoms atom name hmem _ ih =>
        simp only [toLeaTTaAtom, Metta.Atom.vars, List.mem_flatten]
        refine ⟨(toLeaTTaAtom atom).vars, ?_, ih⟩
        exact List.mem_map.mpr
          ⟨toLeaTTaAtom atom, mem_toLeaTTaAtoms_of_mem hmem, rfl⟩
  · intro hmem
    let AtomGoal : Atom → Prop := fun candidate => ∀ name',
      name' ∈ (toLeaTTaAtom candidate).vars →
        Spec.Match.Merge.AtomOccurs candidate name'
    let ListGoal : List Atom → Prop := fun candidates => ∀ name',
      name' ∈ ((toLeaTTaAtoms candidates).map Metta.Atom.vars).flatten →
        ∃ candidate ∈ candidates,
          Spec.Match.Merge.AtomOccurs candidate name'
    have hrec : ∀ candidate, AtomGoal candidate := by
      apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
      · intro symbol name' h
        simp [toLeaTTaAtom, Metta.Atom.vars] at h
      · intro candidate name' h
        have heq : name' = candidate := by
          simpa [toLeaTTaAtom, Metta.Atom.vars] using h
        subst name'
        exact .var candidate
      · intro grounded name' h
        simp [toLeaTTaAtom, Metta.Atom.vars] at h
      · intro candidates ih name' h
        obtain ⟨candidate, hcandidate, hoccurs⟩ := ih name' (by
          simpa [toLeaTTaAtom, Metta.Atom.vars] using h)
        exact .expression hcandidate hoccurs
      · intro name' h
        simp [toLeaTTaAtoms] at h
      · intro candidate candidates ihCandidate ihCandidates name' h
        simp only [toLeaTTaAtoms, List.map_cons, List.flatten_cons,
          List.mem_append] at h
        rcases h with hhead | htail
        · exact ⟨candidate, by simp, ihCandidate name' hhead⟩
        · obtain ⟨found, hfound, hoccurs⟩ :=
            ihCandidates name' htail
          exact ⟨found, by simp [hfound], hoccurs⟩
    exact hrec atom name hmem

theorem assignment_key_mem_bindingSupport
    {bindings : Bindings} {key : String} {value : Atom}
    (hassignment : (key, value) ∈ bindings.assignments) :
    key ∈ bindingSupport bindings := by
  simp only [bindingSupport, List.mem_toFinset, List.mem_append,
    List.mem_flatMap]
  exact Or.inl ⟨(key, value), hassignment, by simp⟩

theorem assignment_value_var_mem_bindingSupport
    {bindings : Bindings} {key dependency : String} {value : Atom}
    (hassignment : (key, value) ∈ bindings.assignments)
    (hdependency : Spec.Match.Merge.AtomOccurs value dependency) :
    dependency ∈ bindingSupport bindings := by
  simp only [bindingSupport, List.mem_toFinset, List.mem_append,
    List.mem_flatMap]
  exact Or.inl ⟨(key, value), hassignment,
    List.mem_cons_of_mem _
      (atomOccurs_iff_mem_translated_vars.mp hdependency)⟩

theorem equality_left_mem_bindingSupport
    {bindings : Bindings} {left right : String}
    (hequality : (left, right) ∈ bindings.equalities) :
    left ∈ bindingSupport bindings := by
  simp only [bindingSupport, List.mem_toFinset, List.mem_append,
    List.mem_flatMap]
  exact Or.inr ⟨(left, right), hequality, by simp⟩

theorem equality_right_mem_bindingSupport
    {bindings : Bindings} {left right : String}
    (hequality : (left, right) ∈ bindings.equalities) :
    right ∈ bindingSupport bindings := by
  simp only [bindingSupport, List.mem_toFinset, List.mem_append,
    List.mem_flatMap]
  exact Or.inr ⟨(left, right), hequality, by simp⟩

/-- Equality closure cannot leave the finite support of a binding record. -/
theorem mem_bindingSupport_of_mem_eqClass
    {bindings : Bindings} {start finish : String}
    (hstart : start ∈ bindingSupport bindings)
    (hclass : finish ∈ bindings.eqClass start) :
    finish ∈ bindingSupport bindings := by
  by_cases heq : finish = start
  · simpa [heq] using hstart
  have hreach := EqualityClosure.mem_eqClass_iff_reachable.mp hclass
  apply hreach.elim
  intro walk
  have hsupport : finish ∈
      start :: EqualityClosure.edgeNodes bindings.equalities :=
    EqualityClosure.walk_support_subset_start_edgeNodes walk
      walk.end_mem_support
  rcases List.mem_cons.mp hsupport with hfinish | hedge
  · exact (heq hfinish).elim
  · simp only [EqualityClosure.edgeNodes, List.mem_flatMap] at hedge
    obtain ⟨edge, hedgeMem, hendpoint⟩ := hedge
    rcases edge with ⟨left, right⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hendpoint
    rcases hendpoint with rfl | rfl
    · exact equality_left_mem_bindingSupport hedgeMem
    · exact equality_right_mem_bindingSupport hedgeMem

/-- Both endpoints of a semantic class-dependency edge lie in the finite
support extracted from the record. -/
theorem classDepends_endpoints_mem_bindingSupport
    {bindings : Bindings} {source target : String}
    (hdepends : Spec.Match.Merge.ClassDepends bindings source target) :
    source ∈ bindingSupport bindings ∧
      target ∈ bindingSupport bindings := by
  rcases hdepends with
    ⟨key, value, dependency, hassignment, hsource,
      hoccurs, htarget, hproper⟩
  have hkey := assignment_key_mem_bindingSupport hassignment
  have hdependency :=
    assignment_value_var_mem_bindingSupport hassignment hoccurs
  exact ⟨mem_bindingSupport_of_mem_eqClass hkey hsource,
    mem_bindingSupport_of_mem_eqClass hdependency htarget⟩

/-! ## The well-founded class-dependency order -/

/-- A dependency node carries proof that it occurs in the finite binding
record. -/
abbrev DependencyNode (bindings : Bindings) :=
  {name : String // name ∈ bindingSupport bindings}

/-- Reverse transitive dependency: a target is smaller than every class whose
stored value depends on it.  This is the orientation required for recursive
evaluation of compound class values. -/
def DependencyOrder (bindings : Bindings) :
    DependencyNode bindings → DependencyNode bindings → Prop :=
  fun target source =>
    Relation.TransGen (Spec.Match.Merge.ClassDepends bindings)
      source.1 target.1

/-- The spec semantic loop filter is precisely enough to make recursive
class evaluation well-founded on the finite support of the record. -/
theorem dependencyOrder_wellFounded
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings) :
    WellFounded (DependencyOrder bindings) := by
  letI : IsStrictOrder (DependencyNode bindings)
      (DependencyOrder bindings) := {
    irrefl := fun node hcycle => hloopFree node.1 hcycle
    trans := fun left middle right hleft hright =>
      Relation.TransGen.trans hright hleft }
  rw [← Set.wellFoundedOn_univ]
  exact Set.finite_univ.wellFoundedOn

/-- A direct dependency can always be reified as a smaller support node. -/
theorem dependencyNode_lt
    {bindings : Bindings} {source : DependencyNode bindings}
    {target : String}
    (hdepends : Spec.Match.Merge.ClassDepends
      bindings source.1 target) :
    ∃ targetNode : DependencyNode bindings,
      targetNode.1 = target ∧ DependencyOrder bindings targetNode source := by
  have htarget := (classDepends_endpoints_mem_bindingSupport hdepends).2
  exact ⟨⟨target, htarget⟩, rfl, .single hdepends⟩

/-! ## Canonical class evaluation -/

/-- Every stored assignment value is non-variable.  specification matcher outputs have
this property because variable/variable matches are represented by equality
edges rather than value assignments. -/
def AssignmentsNonVariable (bindings : Bindings) : Prop :=
  ∀ key value, (key, value) ∈ bindings.assignments →
    Spec.Match.Merge.isVariableB value = false

/-- A variable occurring properly inside a non-variable spec atom becomes
strictly smaller than the interpreted whole atom under every valuation.  The
strictness is structural: symbols and grounded atoms have no occurrences,
while an expression contributes one constructor above the child containing
the variable. -/
theorem size_valuation_lt_apply_of_atomOccurs_nonvariable
    (valuation : String → Metta.Atom) {value : Atom} {dependency : String}
    (hnonvariable : Spec.Match.Merge.isVariableB value = false)
    (hoccurs : Spec.Match.Merge.AtomOccurs value dependency) :
    (valuation dependency).size <
      (applyClassSolution valuation (toLeaTTaAtom value)).size := by
  cases value with
  | symbol symbol => cases hoccurs
  | var name => simp [Spec.Match.Merge.isVariableB] at hnonvariable
  | grounded grounded => cases hoccurs
  | expression atoms =>
      cases hoccurs with
      | @expression _ child _ hchild hoccursChild =>
          have hdependency : dependency ∈ (toLeaTTaAtom child).vars :=
            atomOccurs_iff_mem_translated_vars.mp hoccursChild
          have hle :=
            size_applyClassSolution_ge_of_mem_vars valuation dependency
              (toLeaTTaAtom child) hdependency
          have hchildTranslated :
              toLeaTTaAtom child ∈ toLeaTTaAtoms atoms := by
            exact mem_toLeaTTaAtoms_of_mem hchild
          have hchildApplied :
              applyClassSolution valuation (toLeaTTaAtom child) ∈
                (toLeaTTaAtoms atoms).map
                  (applyClassSolution valuation) := by
            exact List.mem_map.mpr
              ⟨toLeaTTaAtom child, hchildTranslated, rfl⟩
          have hmemSize :
              (applyClassSolution valuation (toLeaTTaAtom child)).size ∈
                ((toLeaTTaAtoms atoms).map
                  (applyClassSolution valuation)).map Metta.Atom.size := by
            exact List.mem_map.mpr
              ⟨applyClassSolution valuation (toLeaTTaAtom child),
                hchildApplied, rfl⟩
          have hsum :
              (applyClassSolution valuation (toLeaTTaAtom child)).size ≤
                (((toLeaTTaAtoms atoms).map
                  (applyClassSolution valuation)).map Metta.Atom.size).sum :=
            List.single_le_sum (by intro _ _; omega) _ hmemSize
          simp only [toLeaTTaAtom, applyClassSolution, Metta.Atom.size]
          omega

/-- Every dependency edge in a satisfiable normalized binding record strictly
decreases the size of the satisfying valuation.  Equality-class endpoints are
identified by the valuation; the proper occurrence inside the stored
non-variable value supplies the strict decrease. -/
theorem size_valuation_lt_of_classDepends
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hnonvariable : AssignmentsNonVariable bindings)
    (hsatisfied : HEBindingSatisfied valuation bindings)
    {source target : String}
    (hdepends : Spec.Match.Merge.ClassDepends bindings source target) :
    (valuation target).size < (valuation source).size := by
  rcases hdepends with
    ⟨key, value, dependency, hassignment, hsource,
      hoccurs, htarget, _⟩
  have hproper := size_valuation_lt_apply_of_atomOccurs_nonvariable
    valuation (hnonvariable key value hassignment) hoccurs
  have hsourceEq := hsatisfied.eq_of_mem_eqClass hsource
  have htargetEq := hsatisfied.eq_of_mem_eqClass htarget
  have hassignmentEq := hsatisfied.1 key value hassignment
  calc
    (valuation target).size = (valuation dependency).size :=
      congrArg Metta.Atom.size htargetEq.symm
    _ < (applyClassSolution valuation (toLeaTTaAtom value)).size := hproper
    _ = (valuation key).size := congrArg Metta.Atom.size hassignmentEq.symm
    _ = (valuation source).size := congrArg Metta.Atom.size hsourceEq

/-- A finite-term model rules out every semantic dependency cycle in a binding
record whose assignments are genuine non-variable values.  This is strictly
weaker than reconciliation provenance: it proves acyclicity, not that the
record contains every equality needed by the canonical valuation. -/
theorem semanticLoopFree_of_satisfied_nonvariable
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    (hnonvariable : AssignmentsNonVariable bindings) :
    Spec.Match.Merge.SemanticLoopFree bindings := by
  intro name hcycle
  have hstrict : ∀ {source target},
      Spec.Match.Merge.ClassDepends bindings source target →
        (valuation target).size < (valuation source).size :=
    fun hdepends =>
      size_valuation_lt_of_classDepends hnonvariable hsatisfied hdepends
  have hstrictPath : ∀ {source target},
      Relation.TransGen (Spec.Match.Merge.ClassDepends bindings)
          source target →
        (valuation target).size < (valuation source).size := by
    intro source target path
    induction path with
    | single hstep => exact hstrict hstep
    | tail hstep hlast ih => exact (hstrict hlast).trans ih
  have himpossible : (valuation name).size < (valuation name).size :=
    hstrictPath hcycle
  exact (Nat.lt_irrefl _ himpossible)

/-- Equality-class membership is symmetric. -/
theorem mem_eqClass_symm {bindings : Bindings} {left right : String}
    (hmem : right ∈ bindings.eqClass left) :
    left ∈ bindings.eqClass right := by
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hmem ⊢
  exact hmem.symm

/-- The stable representative is a member of its own equality class. -/
theorem eqRepresentative_mem_eqClass (bindings : Bindings) (name : String) :
    bindings.eqRepresentative name ∈ bindings.eqClass name := by
  have hself : name ∈ bindings.eqClassOrdered name :=
    EqualityClosure.mem_eqClassOrdered_iff.mpr
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  unfold Bindings.eqRepresentative
  generalize hordered : bindings.eqClassOrdered name = ordered at hself ⊢
  cases ordered with
  | nil => simp at hself
  | cons first rest =>
      apply EqualityClosure.mem_eqClassOrdered_iff.mp
      rw [hordered]
      simp

/-- Connected variables have the same stable representative. -/
theorem eqRepresentative_eq_of_mem_eqClass
    {bindings : Bindings} {left right : String}
    (hmem : right ∈ bindings.eqClass left) :
    bindings.eqRepresentative left = bindings.eqRepresentative right := by
  have hrightSelf : right ∈ bindings.eqClassOrdered right :=
    EqualityClosure.mem_eqClassOrdered_iff.mpr
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  have hordered := EqualityClosure.eqClassOrdered_eq_of_reachable
    (EqualityClosure.mem_eqClass_iff_reachable.mp hmem)
  unfold Bindings.eqRepresentative
  rw [hordered]
  generalize hlist : bindings.eqClassOrdered right = ordered at hrightSelf ⊢
  cases ordered with
  | nil => simp at hrightSelf
  | cons first rest => rfl

/-- Reify the stable representative of a support node as another support
node. -/
def representativeNode {bindings : Bindings}
    (node : DependencyNode bindings) : DependencyNode bindings :=
  ⟨bindings.eqRepresentative node.1,
    mem_bindingSupport_of_mem_eqClass node.2
      (eqRepresentative_mem_eqClass bindings node.1)⟩

/-- One stored assignment whose key belongs to a queried equality class. -/
abbrev ClassAssignment (bindings : Bindings) (name : String) :=
  {entry : String × Atom //
    entry ∈ bindings.assignments ∧ entry.1 ∈ bindings.eqClass name}

/-- Choose one class assignment when one exists.  The choice is deliberately
abstract: the model theorem must prove that every reconciled class value has
the same observation, rather than depending on assignment-list chronology. -/
noncomputable def chosenClassAssignment (bindings : Bindings) (name : String) :
    Option (ClassAssignment bindings name) := by
  classical
  exact if h : Nonempty (ClassAssignment bindings name) then
    some (Classical.choice h)
  else
    none

private theorem classDepends_of_chosen_assignment
    {bindings : Bindings} {source : DependencyNode bindings}
    (assignment : ClassAssignment bindings source.1)
    {dependency : String}
    (hnonvariable : AssignmentsNonVariable bindings)
    (hoccurs : Spec.Match.Merge.AtomOccurs assignment.1.2 dependency) :
    Spec.Match.Merge.ClassDepends bindings source.1
      (bindings.eqRepresentative dependency) := by
  have hassignment := assignment.2.1
  have hkeyClass := assignment.2.2
  refine ⟨assignment.1.1, assignment.1.2, dependency, hassignment,
    mem_eqClass_symm hkeyClass, hoccurs,
    eqRepresentative_mem_eqClass bindings dependency, ?_⟩
  intro halias
  have hvalueVar :
      Spec.Match.Merge.isVariableB assignment.1.2 = true := by
    rw [halias.1]
    rfl
  rw [hnonvariable assignment.1.1 assignment.1.2 hassignment] at hvalueVar
  contradiction

/-- Support node of a variable occurring in the selected class value. -/
def chosenDependencyNode
    {bindings : Bindings} {source : DependencyNode bindings}
    (assignment : ClassAssignment bindings source.1)
    {dependency : String}
    (hoccurs : Spec.Match.Merge.AtomOccurs assignment.1.2 dependency) :
    DependencyNode bindings :=
  ⟨bindings.eqRepresentative dependency,
    mem_bindingSupport_of_mem_eqClass
      (assignment_value_var_mem_bindingSupport
        assignment.2.1 hoccurs)
      (eqRepresentative_mem_eqClass bindings dependency)⟩

theorem chosenDependencyNode_lt
    {bindings : Bindings} {source : DependencyNode bindings}
    (assignment : ClassAssignment bindings source.1)
    {dependency : String}
    (hnonvariable : AssignmentsNonVariable bindings)
    (hoccurs : Spec.Match.Merge.AtomOccurs assignment.1.2 dependency) :
    DependencyOrder bindings
      (chosenDependencyNode assignment hoccurs) source :=
  .single (classDepends_of_chosen_assignment assignment hnonvariable hoccurs)

/-- The selected assignment of a class evaluates recursively through strictly
smaller dependency classes.  Valueless classes denote their stable
representative variable. -/
noncomputable def canonicalNodeValue
    (bindings : Bindings)
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings) :
    DependencyNode bindings → Metta.Atom := by
  classical
  exact (dependencyOrder_wellFounded hloopFree).fix fun source recurse =>
      match chosenClassAssignment bindings source.1 with
      | none => .var (bindings.eqRepresentative source.1)
      | some assignment =>
          applyClassSolution
            (fun dependency =>
              if hoccurs : Spec.Match.Merge.AtomOccurs
                  assignment.1.2 dependency then
                recurse (chosenDependencyNode assignment hoccurs)
                  (chosenDependencyNode_lt assignment hnonvariable hoccurs)
              else
                .var dependency)
            (toLeaTTaAtom assignment.1.2)

/-- Total canonical valuation: support variables use their class
representative's well-founded value; variables absent from the record remain
themselves. -/
noncomputable def canonicalValuation
    (bindings : Bindings)
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings) :
    String → Metta.Atom := fun name =>
  if hsupport : name ∈ bindingSupport bindings then
    canonicalNodeValue bindings hloopFree hnonvariable
      (representativeNode ⟨name, hsupport⟩)
  else
    .var name

private theorem applyClassSolution_congr_of_eq_on_vars
    (left right : String → Metta.Atom) :
    ∀ atom : Metta.Atom,
      (∀ name, name ∈ atom.vars → left name = right name) →
        applyClassSolution left atom = applyClassSolution right atom := by
  intro atom
  induction atom with
  | sym symbol => intro _; simp [applyClassSolution]
  | var name =>
      intro h
      simpa [applyClassSolution] using h name (by simp [Metta.Atom.vars])
  | gnd grounded => intro _; simp [applyClassSolution]
  | expr atoms ih =>
      intro h
      simp only [applyClassSolution]
      congr 1
      apply List.map_congr_left
      intro child hchild
      apply ih child hchild
      intro name hname
      apply h name
      simpa [Metta.Atom.vars] using List.mem_flatten.mpr
        ⟨child.vars, List.mem_map.mpr ⟨child, hchild, rfl⟩, hname⟩

/-- At a variable occurring in the selected value, the recursive call used by
the well-founded evaluator is exactly the total canonical valuation. -/
theorem canonicalValuation_eq_chosenDependencyNode
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (assignment : ClassAssignment bindings source.1)
    {dependency : String}
    (hoccurs : Spec.Match.Merge.AtomOccurs assignment.1.2 dependency) :
    canonicalValuation bindings hloopFree hnonvariable dependency =
      canonicalNodeValue bindings hloopFree hnonvariable
        (chosenDependencyNode assignment hoccurs) := by
  have hsupport := assignment_value_var_mem_bindingSupport
    assignment.2.1 hoccurs
  simp only [canonicalValuation, dif_pos hsupport]
  apply congrArg (canonicalNodeValue bindings hloopFree hnonvariable)
  apply Subtype.ext
  rfl

/-- The selected assignment is satisfied by construction: unfolding one
well-founded step yields precisely homomorphic application of the total
canonical valuation to that value. -/
theorem canonicalNodeValue_eq_applyClassSolution_of_chosen
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (assignment : ClassAssignment bindings source.1)
    (hchosen : chosenClassAssignment bindings source.1 = some assignment) :
    canonicalNodeValue bindings hloopFree hnonvariable source =
      applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom assignment.1.2) := by
  classical
  rw [canonicalNodeValue, WellFounded.fix_eq, hchosen]
  apply applyClassSolution_congr_of_eq_on_vars
  intro dependency hdependency
  have hoccurs := atomOccurs_iff_mem_translated_vars.mpr hdependency
  simp only [dif_pos hoccurs]
  exact (canonicalValuation_eq_chosenDependencyNode
    hloopFree hnonvariable assignment hoccurs).symm

/-- A supported but valueless equality class denotes its stable representative
variable under the canonical evaluator. -/
theorem canonicalValuation_eq_var_representative_of_no_classAssignment
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {name : String}
    (hsupport : name ∈ bindingSupport bindings)
    (hnone : ¬Nonempty
      (ClassAssignment bindings (bindings.eqRepresentative name))) :
    canonicalValuation bindings hloopFree hnonvariable name =
      .var (bindings.eqRepresentative name) := by
  classical
  have hrepresentative :
      bindings.eqRepresentative (bindings.eqRepresentative name) =
        bindings.eqRepresentative name :=
    (eqRepresentative_eq_of_mem_eqClass
      (eqRepresentative_mem_eqClass bindings name)).symm
  rw [canonicalValuation, dif_pos hsupport]
  rw [canonicalNodeValue, WellFounded.fix_eq]
  simp only [representativeNode]
  rw [show chosenClassAssignment bindings
      (bindings.eqRepresentative name) = none by
    simp [chosenClassAssignment, hnone]]
  simp [hrepresentative]

/-- The canonical valuation is constant on every explicit equality class. -/
theorem canonicalValuation_eq_of_mem_eqClass
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {left right : String}
    (hleftSupport : left ∈ bindingSupport bindings)
    (hmem : right ∈ bindings.eqClass left) :
    canonicalValuation bindings hloopFree hnonvariable left =
      canonicalValuation bindings hloopFree hnonvariable right := by
  have hrightSupport :=
    mem_bindingSupport_of_mem_eqClass hleftSupport hmem
  have hrepresentative := eqRepresentative_eq_of_mem_eqClass hmem
  simp only [canonicalValuation, dif_pos hleftSupport,
    dif_pos hrightSupport]
  apply congrArg (canonicalNodeValue bindings hloopFree hnonvariable)
  apply Subtype.ext
  exact hrepresentative

/-- In particular, every raw equality edge is satisfied by the canonical
valuation. -/
theorem canonicalValuation_satisfies_equalities
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings) :
    ∀ left right, (left, right) ∈ bindings.equalities →
      canonicalValuation bindings hloopFree hnonvariable left =
        canonicalValuation bindings hloopFree hnonvariable right := by
  intro left right hedge
  apply canonicalValuation_eq_of_mem_eqClass hloopFree hnonvariable
    (equality_left_mem_bindingSupport hedge)
  rw [EqualityClosure.mem_eqClass_iff_reachable]
  by_cases heq : left = right
  · subst right
    exact .rfl
  · exact (show (EqualityClosure.edgeGraph bindings.equalities).Adj left right
        from ⟨heq, Or.inl hedge⟩).reachable

/-- Homomorphic substitutions compose. -/
theorem applyClassSolution_comp
    (outer inner : String → Metta.Atom) :
    ∀ atom : Metta.Atom,
      applyClassSolution outer (applyClassSolution inner atom) =
        applyClassSolution
          (fun name => applyClassSolution outer (inner name)) atom := by
  intro atom
  induction atom with
  | sym symbol => simp [applyClassSolution]
  | var name => simp [applyClassSolution]
  | gnd grounded => simp [applyClassSolution]
  | expr atoms ih =>
      simp only [applyClassSolution, List.map_map]
      congr 1
      exact List.map_congr_left fun child hchild => ih child hchild

/-- Every concrete model absorbs the canonical class evaluator.  Applying a
satisfying valuation after one canonical evaluation yields the same concrete
valuation.  This theorem needs loop freedom and assignment shape, but not yet
class coherence: the selected assignment is satisfied by every model, and all
of its recursive dependencies are strictly smaller. -/
theorem apply_canonicalNodeValue_eq_of_satisfied
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {specific : String → Metta.Atom}
    (hspecific : HEBindingSatisfied specific bindings) :
    ∀ source : DependencyNode bindings,
      applyClassSolution specific
          (canonicalNodeValue bindings hloopFree hnonvariable source) =
        specific source.1 := by
  intro source
  induction source using (dependencyOrder_wellFounded hloopFree).induction with
  | h source ih =>
      classical
      cases hchosen : chosenClassAssignment bindings source.1 with
      | none =>
          rw [canonicalNodeValue, WellFounded.fix_eq, hchosen]
          simp only [applyClassSolution]
          exact (hspecific.eq_of_mem_eqClass
            (eqRepresentative_mem_eqClass bindings source.1)).symm
      | some assignment =>
          rw [canonicalNodeValue_eq_applyClassSolution_of_chosen
            hloopFree hnonvariable assignment hchosen,
            applyClassSolution_comp]
          calc
            applyClassSolution
                (fun name => applyClassSolution specific
                  (canonicalValuation bindings hloopFree hnonvariable name))
                (toLeaTTaAtom assignment.1.2) =
                applyClassSolution specific
                  (toLeaTTaAtom assignment.1.2) := by
              apply applyClassSolution_congr_of_eq_on_vars
              intro dependency hdependency
              have hoccurs :=
                atomOccurs_iff_mem_translated_vars.mpr hdependency
              rw [canonicalValuation_eq_chosenDependencyNode
                hloopFree hnonvariable assignment hoccurs]
              exact (ih (chosenDependencyNode assignment hoccurs)
                  (chosenDependencyNode_lt assignment hnonvariable hoccurs)).trans
                ((hspecific.eq_of_mem_eqClass
                  (eqRepresentative_mem_eqClass bindings dependency)).symm)
            _ = specific assignment.1.1 :=
              (hspecific.1 assignment.1.1 assignment.1.2
                assignment.2.1).symm
            _ = specific source.1 :=
              (hspecific.eq_of_mem_eqClass assignment.2.2).symm

/-- The total canonical valuation is absorbed by every concrete model. -/
theorem apply_canonicalValuation_eq_of_satisfied
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {specific : String → Metta.Atom}
    (hspecific : HEBindingSatisfied specific bindings) :
    ∀ name,
      applyClassSolution specific
          (canonicalValuation bindings hloopFree hnonvariable name) =
        specific name := by
  intro name
  classical
  by_cases hsupport : name ∈ bindingSupport bindings
  · rw [canonicalValuation, dif_pos hsupport,
      apply_canonicalNodeValue_eq_of_satisfied
        hloopFree hnonvariable hspecific]
    exact (hspecific.eq_of_mem_eqClass
      (eqRepresentative_mem_eqClass bindings name)).symm
  · rw [canonicalValuation, dif_neg hsupport]
    simp [applyClassSolution]

/-- The remaining consistency obligation for a spec derivation: every stored
assignment in a class must evaluate to the canonical value of that class.
This property is strictly stronger than loop freedom—`{x ↦ a, x ↦ b}` is
acyclic but fails it—and is exactly what reconciliation provenance supplies. -/
def CanonicalClassCoherent
    (bindings : Bindings)
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings) : Prop :=
  ∀ source : DependencyNode bindings,
    ∀ assignment : ClassAssignment bindings source.1,
      canonicalNodeValue bindings hloopFree hnonvariable source =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom assignment.1.2)

/-- Class coherence plus semantic loop freedom produces an actual syntactic
Herbrand model of the binding record.  Equality edges are handled by the
stable class representative; assignment equations are exactly the coherence
premise. -/
theorem canonicalValuation_satisfies_of_classCoherent
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hcoherent : CanonicalClassCoherent bindings hloopFree hnonvariable) :
    HEBindingSatisfied
      (canonicalValuation bindings hloopFree hnonvariable) bindings := by
  constructor
  · intro key value hassignment
    have hkeySupport := assignment_key_mem_bindingSupport hassignment
    let keyNode : DependencyNode bindings := ⟨key, hkeySupport⟩
    let source := representativeNode keyNode
    have hkeyClass : key ∈ bindings.eqClass source.1 := by
      exact mem_eqClass_symm (eqRepresentative_mem_eqClass bindings key)
    let assignment : ClassAssignment bindings source.1 :=
      ⟨(key, value), hassignment, hkeyClass⟩
    have hsource := hcoherent source assignment
    simpa only [canonicalValuation, dif_pos hkeySupport] using hsource
  · exact canonicalValuation_satisfies_equalities hloopFree hnonvariable

/-- The class chosen by the canonical evaluator is coherent by construction.
Only agreement of the other class assignments remains for derivation
provenance. -/
theorem canonicalClassCoherent_of_every_assignment_eq_chosen
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hagrees : ∀ (source : DependencyNode bindings)
        (chosen assignment : ClassAssignment bindings source.1),
      chosenClassAssignment bindings source.1 = some chosen →
      applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom chosen.1.2) =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom assignment.1.2)) :
    CanonicalClassCoherent bindings hloopFree hnonvariable := by
  intro source assignment
  cases hchosen : chosenClassAssignment bindings source.1 with
  | none =>
      have hempty : ¬Nonempty (ClassAssignment bindings source.1) := by
        intro hnonempty
        simp [chosenClassAssignment, hnonempty] at hchosen
      exact (hempty ⟨assignment⟩).elim
  | some chosen =>
      exact (canonicalNodeValue_eq_applyClassSolution_of_chosen
        hloopFree hnonvariable chosen hchosen).trans
          (hagrees source chosen assignment hchosen)

/-- Conflict-free classes are the base case of reconciliation provenance:
when a class carries at most one distinct assignment, canonical coherence is
immediate. -/
theorem canonicalClassCoherent_of_subsingleton_classAssignments
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hsubsingleton : ∀ source : DependencyNode bindings,
      Subsingleton (ClassAssignment bindings source.1)) :
    CanonicalClassCoherent bindings hloopFree hnonvariable := by
  apply canonicalClassCoherent_of_every_assignment_eq_chosen
    hloopFree hnonvariable
  intro source chosen assignment hchosen
  rw [hsubsingleton source |>.elim chosen assignment]

/-- Hence a loop-free record with at most one assignment per equality class
has a canonical model without any reconciliation proof. -/
theorem has_model_of_subsingleton_classAssignments
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hsubsingleton : ∀ source : DependencyNode bindings,
      Subsingleton (ClassAssignment bindings source.1)) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings := by
  refine ⟨canonicalValuation bindings hloopFree hnonvariable, ?_⟩
  exact canonicalValuation_satisfies_of_classCoherent
    hloopFree hnonvariable
    (canonicalClassCoherent_of_subsingleton_classAssignments
      hloopFree hnonvariable hsubsingleton)

/-! ## Semantic refinement algebra -/

/-- A valuation is a specialization of another when it is obtained by applying
one further homomorphic substitution to every image.  This is the semantic
notion needed to carry compatibility through a successful constraint fold;
plain model existence is not closed under intersection. -/
def ValuationRefines
    (specific general : String → Metta.Atom) : Prop :=
  ∃ post : String → Metta.Atom,
    ∀ name, specific name = applyClassSolution post (general name)

/-- The variable-identity valuation acts identically on every atom. -/
theorem applyClassSolution_identity :
    ∀ atom : Metta.Atom,
      applyClassSolution (fun name => Metta.Atom.var name) atom = atom := by
  intro atom
  induction atom with
  | sym symbol => simp [applyClassSolution]
  | var name => simp [applyClassSolution]
  | gnd grounded => simp [applyClassSolution]
  | expr atoms ih =>
      simp only [applyClassSolution]
      congr 1
      calc
        List.map
            (applyClassSolution (fun name => Metta.Atom.var name)) atoms =
            List.map id atoms :=
          List.map_congr_left fun child hchild => ih child hchild
        _ = atoms := List.map_id atoms

theorem ValuationRefines.refl (valuation : String → Metta.Atom) :
    ValuationRefines valuation valuation := by
  refine ⟨fun name => Metta.Atom.var name, fun name => ?_⟩
  exact (applyClassSolution_identity (valuation name)).symm

theorem ValuationRefines.trans
    {most middle least : String → Metta.Atom}
    (hmiddle : ValuationRefines most middle)
    (hleast : ValuationRefines middle least) :
    ValuationRefines most least := by
  rcases hmiddle with ⟨outer, houter⟩
  rcases hleast with ⟨inner, hinner⟩
  refine ⟨fun name => applyClassSolution outer (inner name), fun name => ?_⟩
  rw [houter name, hinner name, applyClassSolution_comp]

/-- Refinement commutes with homomorphic interpretation of every atom. -/
theorem ValuationRefines.apply_eq_applyClassSolution
    {specific general : String → Metta.Atom}
    (hrefines : ValuationRefines specific general) :
    ∃ post : String → Metta.Atom,
      ∀ atom,
        applyClassSolution specific atom =
          applyClassSolution post (applyClassSolution general atom) := by
  rcases hrefines with ⟨post, hpost⟩
  refine ⟨post, fun atom => ?_⟩
  rw [applyClassSolution_comp]
  apply applyClassSolution_congr_of_eq_on_vars
  intro name hname
  exact hpost name

/-- Every specialization of a satisfying valuation still satisfies the same
binding equations. -/
theorem ValuationRefines.bindingSatisfied
    {specific general : String → Metta.Atom} {bindings : Bindings}
    (hrefines : ValuationRefines specific general)
    (hsatisfied : HEBindingSatisfied general bindings) :
    HEBindingSatisfied specific bindings := by
  obtain ⟨post, happly⟩ := hrefines.apply_eq_applyClassSolution
  constructor
  · intro key value hassignment
    have hgeneral := hsatisfied.1 key value hassignment
    have hkey : specific key = applyClassSolution post (general key) := by
      simpa [applyClassSolution] using happly (.var key)
    calc
      specific key = applyClassSolution post (general key) := hkey
      _ = applyClassSolution post
          (applyClassSolution general (toLeaTTaAtom value)) :=
            congrArg (applyClassSolution post) hgeneral
      _ = applyClassSolution specific (toLeaTTaAtom value) :=
            (happly (toLeaTTaAtom value)).symm
  · intro left right hequality
    have hgeneral := hsatisfied.2 left right hequality
    have hleft : specific left = applyClassSolution post (general left) := by
      simpa [applyClassSolution] using happly (.var left)
    have hright : specific right = applyClassSolution post (general right) := by
      simpa [applyClassSolution] using happly (.var right)
    calc
      specific left = applyClassSolution post (general left) := hleft
      _ = applyClassSolution post (general right) :=
            congrArg (applyClassSolution post) hgeneral
      _ = specific right := hright.symm

/-- A most-general solution presents every model of the binding record as one
of its specializations. -/
def MostGeneralSolution
    (bindings : Bindings) (general : String → Metta.Atom) : Prop :=
  HEBindingSatisfied general bindings ∧
    ∀ specific, HEBindingSatisfied specific bindings →
      ValuationRefines specific general

/-- The identity valuation is the most-general solution of the empty record. -/
theorem identity_mostGeneralSolution_empty :
    MostGeneralSolution Bindings.empty (fun name => .var name) := by
  constructor
  · exact hesat_empty (fun name => .var name)
  · intro specific hsatisfied
    refine ⟨specific, fun name => ?_⟩
    simp [applyClassSolution]

/-- Once reconciliation provenance supplies class coherence, the canonical
model is principal: every other model is obtained by one further homomorphic
substitution.  Thus the model construction also provides the strongest
solution-theoretic invariant needed by recursive merge-back. -/
theorem canonicalValuation_mostGeneralSolution_of_classCoherent
    {bindings : Bindings}
    (hloopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hcoherent : CanonicalClassCoherent bindings hloopFree hnonvariable) :
    MostGeneralSolution bindings
      (canonicalValuation bindings hloopFree hnonvariable) := by
  constructor
  · exact canonicalValuation_satisfies_of_classCoherent
      hloopFree hnonvariable hcoherent
  · intro specific hspecific
    refine ⟨specific, fun name => ?_⟩
    exact (apply_canonicalValuation_eq_of_satisfied
      hloopFree hnonvariable hspecific name).symm

/-! ## Monotone record growth -/

/-- Literal record inclusion.  specification merge-back never removes a constraint
from its live left accumulator, even when a proposed right constraint is
reconciled rather than copied literally. -/
def BindingSubrecord (before after : Bindings) : Prop :=
  (∀ assignment, assignment ∈ before.assignments →
    assignment ∈ after.assignments) ∧
  (∀ equality, equality ∈ before.equalities →
    equality ∈ after.equalities)

theorem BindingSubrecord.refl (bindings : Bindings) :
    BindingSubrecord bindings bindings :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem BindingSubrecord.trans {first second third : Bindings}
    (hfirst : BindingSubrecord first second)
    (hsecond : BindingSubrecord second third) :
    BindingSubrecord first third :=
  ⟨fun assignment h => hsecond.1 assignment (hfirst.1 assignment h),
    fun equality h => hsecond.2 equality (hfirst.2 equality h)⟩

/-- Literal equality-edge inclusion induces inclusion of the corresponding
undirected equality graphs. -/
theorem BindingSubrecord.edgeGraph_mono {before after : Bindings}
    (hsubrecord : BindingSubrecord before after) :
    EqualityClosure.edgeGraph before.equalities ≤
      EqualityClosure.edgeGraph after.equalities := by
  intro left right hadjacent
  rw [EqualityClosure.edgeGraph_adj_iff] at hadjacent ⊢
  refine ⟨hadjacent.1, ?_⟩
  exact hadjacent.2.elim
    (fun hedge => Or.inl (hsubrecord.2 _ hedge))
    (fun hedge => Or.inr (hsubrecord.2 _ hedge))

/-- Equality-class membership can only grow when a binding record is extended. -/
theorem BindingSubrecord.mem_eqClass {before after : Bindings}
    (hsubrecord : BindingSubrecord before after)
    {start finish : String}
    (hclass : finish ∈ before.eqClass start) :
    finish ∈ after.eqClass start := by
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  exact (SimpleGraph.Reachable.mono' hsubrecord.edgeGraph_mono)
    start finish hclass

/-- Non-variable assignment shape descends to every literal subrecord. -/
theorem AssignmentsNonVariable.of_subrecord {before after : Bindings}
    (hafter : AssignmentsNonVariable after)
    (hsubrecord : BindingSubrecord before after) :
    AssignmentsNonVariable before := by
  intro key value hassignment
  exact hafter key value (hsubrecord.1 _ hassignment)

/-- Under the non-variable assignment invariant, every dependency already
present in a subrecord remains a dependency after further merge-back.  The
extra side condition in `ClassDepends` is automatic because a stored value
cannot be a bare variable. -/
theorem BindingSubrecord.classDepends {before after : Bindings}
    (hsubrecord : BindingSubrecord before after)
    (hnonvariable : AssignmentsNonVariable before)
    {source target : String}
    (hdepends : Spec.Match.Merge.ClassDepends before source target) :
    Spec.Match.Merge.ClassDepends after source target := by
  rcases hdepends with
    ⟨key, value, dependency, hassignment, hsource, hoccurs, htarget, _⟩
  refine ⟨key, value, dependency,
    hsubrecord.1 _ hassignment,
    hsubrecord.mem_eqClass hsource,
    hoccurs,
    hsubrecord.mem_eqClass htarget, ?_⟩
  intro hproperAlias
  have hvalueVariable : Spec.Match.Merge.isVariableB value = true := by
    rw [hproperAlias.1]
    rfl
  rw [hnonvariable key value hassignment] at hvalueVariable
  contradiction

/-- A loop in a subrecord would remain a loop in every non-variable extension.
Consequently semantic loop freedom descends from an ambient final matcher
record to every live accumulator literally contained in it. -/
theorem BindingSubrecord.semanticLoopFree {before after : Bindings}
    (hsubrecord : BindingSubrecord before after)
    (hnonvariable : AssignmentsNonVariable before)
    (hafter : Spec.Match.Merge.SemanticLoopFree after) :
    Spec.Match.Merge.SemanticLoopFree before := by
  intro name hcycle
  apply hafter name
  exact Relation.TransGen.mono
    (fun _ _ hstep => hsubrecord.classDepends hnonvariable hstep) hcycle

theorem bindingSubrecord_assign_of_not_isBound (bindings : Bindings)
    (key : String) (value : Atom)
    (hnotbound : bindings.isBound key = false) :
    BindingSubrecord bindings (bindings.assign key value) := by
  unfold Bindings.assign
  rw [hnotbound]
  constructor
  · intro assignment hmem
    exact List.mem_append_left _ hmem
  · intro equality hmem
    exact hmem

theorem bindingSubrecord_addEquality (bindings : Bindings)
    (left right : String) :
    BindingSubrecord bindings (bindings.addEquality left right) := by
  constructor
  · intro assignment hmem
    exact hmem
  · intro equality hmem
    exact List.mem_append_left _ hmem

/-- Every declarative spec merge contains its entire live left accumulator.
This is proved on the pure six-way relation and is independent of constraint
fold order. -/
theorem mergeRel_left_subrecord
    {left right out : Bindings}
    (hmerge : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic left right out) :
    BindingSubrecord left out := by
  apply Spec.Match.Merge.MergeRel.rec
    (motive_1 := fun _ _ out _ =>
      BindingSubrecord Bindings.empty out)
    (motive_2 := fun _ _ seed out _ => BindingSubrecord seed out)
    (motive_3 := fun bindings _ _ out _ => BindingSubrecord bindings out)
    (motive_4 := fun bindings _ _ out _ => BindingSubrecord bindings out)
    (motive_5 := fun seed _ out _ => BindingSubrecord seed out)
    (motive_6 := fun left _ out _ => BindingSubrecord left out)
    (t := hmerge)
  next =>
      intro symbol hadmissible
      exact BindingSubrecord.refl Bindings.empty
  next =>
      intro left right hadmissible
      exact bindingSubrecord_addEquality Bindings.empty left right
  next =>
      intro varName value hnonvar hadmissible
      exact bindingSubrecord_assign_of_not_isBound
        Bindings.empty varName value (by
          simp [Bindings.empty, Bindings.isBound, Bindings.lookup])
  next =>
      intro value varName hnonvar hadmissible
      exact bindingSubrecord_assign_of_not_isBound
        Bindings.empty varName value (by
          simp [Bindings.empty, Bindings.isBound, Bindings.lookup])
  next =>
      intro left right out hitems hadmissible ih
      exact ih
  next =>
      intro grounded right out hright hcustom hmatch hadmissible
      rcases hmatch with ⟨hrightEq, hout⟩
      subst right
      subst out
      exact BindingSubrecord.refl Bindings.empty
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hmatch hadmissible
      rcases hmatch with ⟨hleftEq, hout⟩
      subst left
      subst out
      exact BindingSubrecord.refl Bindings.empty
  next =>
      intro left right hleft hright hadmissible
      exact (hleft (by
        simp [Spec.Match.Merge.equalityGroundedSemantic])).elim
  next =>
      intro seed
      exact BindingSubrecord.refl seed
  next =>
      intro left right lefts rights seed matched next out
        hmatch hmerge htail ihMatch ihMerge ihTail
      exact ihMerge.trans ihTail
  next =>
      intro bindings varName value hvalues
      exact bindingSubrecord_assign_of_not_isBound bindings varName value
        (isBound_eq_false_of_classValues_nil hvalues)
  next =>
      intro bindings varName value first rest hvalues hagree hvalue
      exact BindingSubrecord.refl bindings
  next =>
      intro bindings varName value first rest matched out hvalues hagree
        hne hmatch hmerge ihMatch ihMerge
      exact ihMerge
  next =>
      intro bindings varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      exact ihMerge
  next =>
      intro bindings left right values hvalues hagree
      exact bindingSubrecord_addEquality bindings left right
  next =>
      intro bindings left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      exact (bindingSubrecord_addEquality bindings left right).trans ihMerge
  next =>
      intro seed
      exact BindingSubrecord.refl seed
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail
      exact ihAdd.trans ihTail
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail
      exact ihAdd.trans ihTail
  next =>
      intro left right out order horder hfold ihFold
      exact ihFold

/-- A pointwise list match never removes a constraint from its live seed. -/
theorem matchListAccRel_seed_subrecord
    {left right : List Atom} {seed out : Bindings}
    (hmatch : Spec.Match.Merge.MatchListAccRel
      Spec.Match.Merge.equalityGroundedSemantic
      left right seed out) :
    BindingSubrecord seed out := by
  apply Spec.Match.Merge.MatchListAccRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ seed out _ => BindingSubrecord seed out)
    (motive_3 := fun bindings _ _ out _ => BindingSubrecord bindings out)
    (motive_4 := fun bindings _ _ out _ => BindingSubrecord bindings out)
    (motive_5 := fun seed _ out _ => BindingSubrecord seed out)
    (motive_6 := fun left _ out _ => BindingSubrecord left out)
    (t := hmatch)
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next =>
      intro seed
      exact BindingSubrecord.refl seed
  next =>
      intro left right lefts rights seed matched next out
        hhead hmerge htail ihHead ihMerge ihTail
      exact ihMerge.trans ihTail
  next =>
      intro bindings varName value hvalues
      exact bindingSubrecord_assign_of_not_isBound bindings varName value
        (isBound_eq_false_of_classValues_nil hvalues)
  next =>
      intro bindings varName value first rest hvalues hagree hvalue
      exact BindingSubrecord.refl bindings
  next =>
      intro bindings varName value first rest matched out hvalues hagree
        hne hhead hmerge ihHead ihMerge
      exact ihMerge
  next =>
      intro bindings varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      exact ihMerge
  next =>
      intro bindings left right values hvalues hagree
      exact bindingSubrecord_addEquality bindings left right
  next =>
      intro bindings left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge
      exact (bindingSubrecord_addEquality bindings left right).trans ihMerge
  next =>
      intro seed
      exact BindingSubrecord.refl seed
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail
      exact ihAdd.trans ihTail
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail
      exact ihAdd.trans ihTail
  next =>
      intro left right out order horder hfold ihFold
      exact ihFold

/-- Adding one value constraint never removes a live seed constraint. -/
theorem addVarBindingRel_seed_subrecord
    {seed : Bindings} {varName : String} {value : Atom} {out : Bindings}
    (hadd : Spec.Match.Merge.AddVarBindingRel
      Spec.Match.Merge.equalityGroundedSemantic
      seed varName value out) :
    BindingSubrecord seed out := by
  cases hadd with
  | fresh hvalues =>
      exact bindingSubrecord_assign_of_not_isBound _ _ _
        (isBound_eq_false_of_classValues_nil hvalues)
  | same => exact BindingSubrecord.refl seed
  | conflict hvalues hagree hne hmatch hmerge =>
      exact mergeRel_left_subrecord hmerge
  | reconcile hvalues hnotAgree hlist hmerge =>
      exact mergeRel_left_subrecord hmerge

/-- Adding one equality constraint never removes a live seed constraint. -/
theorem addVarEqualityRel_seed_subrecord
    {seed : Bindings} {left right : String} {out : Bindings}
    (hadd : Spec.Match.Merge.AddVarEqualityRel
      Spec.Match.Merge.equalityGroundedSemantic seed left right out) :
    BindingSubrecord seed out := by
  cases hadd with
  | consistent => exact bindingSubrecord_addEquality seed left right
  | reconcile hvalues hnotAgree hlist hmerge =>
      exact (bindingSubrecord_addEquality seed left right).trans
        (mergeRel_left_subrecord hmerge)

/-- Any intermediate accumulator literally included in an admitted final
matcher record inherits semantic loop freedom. -/
theorem semanticLoopFree_of_subrecord_of_match
    {query pattern : Atom} {out before : Bindings}
    (hmatch : Spec.Match.Merge.MatchRel
      Spec.Match.Merge.equalityGroundedSemantic query pattern out)
    (hsubrecord : BindingSubrecord before out)
    (hnonvariable : AssignmentsNonVariable before) :
    Spec.Match.Merge.SemanticLoopFree before := by
  have houtLoopFree : Spec.Match.Merge.SemanticLoopFree out := by
    cases hmatch <;> assumption
  exact hsubrecord.semanticLoopFree hnonvariable houtLoopFree

/-! ## Boundary canaries -/

/-- Acyclicity alone is intentionally not treated as consistency.  This probe
has two non-variable assignments in one equality class but incompatible
constructor heads.  It is a well-formed record shape, yet no successful spec
reconciliation derivation may expose it as a final match result. -/
def incompatibleAcyclicProbe : Bindings :=
  ⟨[("x", .symbol "a"), ("y", .symbol "b")], [("x", "y")]⟩

theorem incompatibleAcyclicProbe_nonvariable :
    AssignmentsNonVariable incompatibleAcyclicProbe := by
  intro key value hassignment
  simp [incompatibleAcyclicProbe] at hassignment
  rcases hassignment with hassignment | hassignment
  · rw [hassignment.2]
    rfl
  · rw [hassignment.2]
    rfl

theorem incompatibleAcyclicProbe_loopFree :
    Spec.Match.Merge.SemanticLoopFree incompatibleAcyclicProbe := by
  have hnostep : ∀ source target,
      ¬Spec.Match.Merge.ClassDepends
        incompatibleAcyclicProbe source target := by
    intro source target hdepends
    rcases hdepends with
      ⟨key, value, dependency, hassignment, hsource, hoccurs, htarget,
        hproper⟩
    simp [incompatibleAcyclicProbe] at hassignment
    rcases hassignment with hassignment | hassignment
    · rw [hassignment.2] at hoccurs
      cases hoccurs
    · rw [hassignment.2] at hoccurs
      cases hoccurs
  intro name hcycle
  cases hcycle with
  | single hstep => exact hnostep _ _ hstep
  | tail _ hstep => exact hnostep _ _ hstep

/-- Negative model oracle: the incompatible acyclic probe really is
unsatisfiable, so any proof using loop freedom as if it implied a model would
be rejected here. -/
theorem incompatibleAcyclicProbe_has_no_model :
    ¬∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation incompatibleAcyclicProbe := by
  rintro ⟨valuation, hsatisfied⟩
  have ha := hsatisfied.1 "x" (.symbol "a") (by
    simp [incompatibleAcyclicProbe])
  have hb := hsatisfied.1 "y" (.symbol "b") (by
    simp [incompatibleAcyclicProbe])
  have hxy := hsatisfied.2 "x" "y" (by
    simp [incompatibleAcyclicProbe])
  have hab : Metta.Atom.sym "a" = Metta.Atom.sym "b" := by
    calc
      Metta.Atom.sym "a" = valuation "x" := by
        simpa [toLeaTTaAtom, applyClassSolution] using ha.symm
      _ = valuation "y" := hxy
      _ = Metta.Atom.sym "b" := by
        simpa [toLeaTTaAtom, applyClassSolution] using hb
  simp at hab

/-- Therefore the missing reconciliation-provenance hypothesis is substantive,
not a proof-irrelevant reformulation of loop freedom. -/
theorem incompatibleAcyclicProbe_not_classCoherent :
    ¬CanonicalClassCoherent incompatibleAcyclicProbe
      incompatibleAcyclicProbe_loopFree
      incompatibleAcyclicProbe_nonvariable := by
  intro hcoherent
  apply incompatibleAcyclicProbe_has_no_model
  exact ⟨canonicalValuation incompatibleAcyclicProbe
      incompatibleAcyclicProbe_loopFree
      incompatibleAcyclicProbe_nonvariable,
    canonicalValuation_satisfies_of_classCoherent
      incompatibleAcyclicProbe_loopFree
      incompatibleAcyclicProbe_nonvariable hcoherent⟩

/-! Satisfiability is also strictly weaker than reconciliation provenance.
The next probe has a concrete model, but its two values for `x` agree only
because that model happens to identify `y` with the symbol `a`; the binding
record itself contains no constraint recording that identification. -/

def satisfiableUnreconciledProbe : Bindings :=
  ⟨[("x", .expression [.symbol "f", .var "y"]),
    ("x", .expression [.symbol "f", .symbol "a"])], []⟩

theorem satisfiableUnreconciledProbe_nonvariable :
    AssignmentsNonVariable satisfiableUnreconciledProbe := by
  intro key value hassignment
  simp [satisfiableUnreconciledProbe] at hassignment
  rcases hassignment with hassignment | hassignment
  · rw [hassignment.2]
    rfl
  · rw [hassignment.2]
    rfl

theorem satisfiableUnreconciledProbe_loopFree :
    Spec.Match.Merge.SemanticLoopFree satisfiableUnreconciledProbe := by
  have hedge : ∀ {source target},
      Spec.Match.Merge.ClassDepends
          satisfiableUnreconciledProbe source target →
        source = "x" ∧ target = "y" := by
    intro source target hdepends
    rcases hdepends with
      ⟨key, value, dependency, hassignment, hsource,
        hoccurs, htarget, _hproper⟩
    simp [satisfiableUnreconciledProbe] at hassignment
    rcases hassignment with hassignment | hassignment
    · rcases hassignment with ⟨rfl, rfl⟩
      have hdependency : dependency = "y" := by
        have hmem := atomOccurs_iff_mem_translated_vars.mp hoccurs
        simpa [toLeaTTaAtom, Metta.Atom.vars] using hmem
      subst dependency
      constructor
      · simpa [satisfiableUnreconciledProbe, Bindings.eqClass,
          Bindings.eqClassAux, Bindings.eqStep] using hsource
      · simpa [satisfiableUnreconciledProbe, Bindings.eqClass,
          Bindings.eqClassAux, Bindings.eqStep] using htarget
    · rcases hassignment with ⟨rfl, rfl⟩
      have hmem := atomOccurs_iff_mem_translated_vars.mp hoccurs
      simp [toLeaTTaAtom, Metta.Atom.vars] at hmem
  intro name hcycle
  have hreach : ∀ {source target},
      Relation.TransGen
          (Spec.Match.Merge.ClassDepends satisfiableUnreconciledProbe)
          source target →
        source = "x" ∧ target = "y" := by
    intro source target hpath
    induction hpath with
    | single h => exact hedge h
    | tail _ h ih => exact ⟨ih.1, (hedge h).2⟩
  have hfinal := hreach hcycle
  rw [hfinal.1] at hfinal
  simp at hfinal

theorem satisfiableUnreconciledProbe_has_model :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation satisfiableUnreconciledProbe := by
  let valuation : String → Metta.Atom := fun name =>
    if name = "x" then .expr [.sym "f", .sym "a"]
    else if name = "y" then .sym "a"
    else .var name
  refine ⟨valuation, ?_⟩
  constructor
  · intro key value hassignment
    simp [satisfiableUnreconciledProbe] at hassignment
    rcases hassignment with hassignment | hassignment
    · rcases hassignment with ⟨rfl, rfl⟩
      simp [valuation, toLeaTTaAtom, applyClassSolution]
    · rcases hassignment with ⟨rfl, rfl⟩
      simp [valuation, toLeaTTaAtom, applyClassSolution]
  · intro left right hequality
    simp [satisfiableUnreconciledProbe] at hequality

/-- Negative canonical-model oracle: even satisfiability plus semantic loop
freedom does not make the canonical class evaluator a model.  The concrete
model above identifies `y` with `a`, but the record contains no constraint
that makes the canonical evaluator perform that identification. -/
theorem satisfiableUnreconciledProbe_canonical_not_model :
    ¬HEBindingSatisfied
      (canonicalValuation satisfiableUnreconciledProbe
        satisfiableUnreconciledProbe_loopFree
        satisfiableUnreconciledProbe_nonvariable)
      satisfiableUnreconciledProbe := by
  let valuation := canonicalValuation satisfiableUnreconciledProbe
    satisfiableUnreconciledProbe_loopFree
    satisfiableUnreconciledProbe_nonvariable
  change ¬HEBindingSatisfied valuation satisfiableUnreconciledProbe
  intro hsatisfied
  have hysupport : "y" ∈ bindingSupport satisfiableUnreconciledProbe := by
    apply assignment_value_var_mem_bindingSupport
      (key := "x") (value := .expression [.symbol "f", .var "y"])
    · simp [satisfiableUnreconciledProbe]
    · exact .expression (by simp) (.var "y")
  have hyrep : satisfiableUnreconciledProbe.eqRepresentative "y" = "y" := by
    simp [satisfiableUnreconciledProbe, Bindings.eqRepresentative,
      Bindings.eqClassOrdered, Bindings.eqVarsInOrder]
  have hynone : ¬Nonempty
      (ClassAssignment satisfiableUnreconciledProbe
        (satisfiableUnreconciledProbe.eqRepresentative "y")) := by
    rw [hyrep]
    rintro ⟨⟨⟨key, value⟩, hassignment, hclass⟩⟩
    simp [satisfiableUnreconciledProbe] at hassignment
    rcases hassignment with hassignment | hassignment <;>
      rcases hassignment with ⟨rfl, rfl⟩ <;>
      simp [satisfiableUnreconciledProbe, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep] at hclass
  have hy : valuation "y" = .var "y" := by
    simpa [valuation, hyrep] using
      (canonicalValuation_eq_var_representative_of_no_classAssignment
        satisfiableUnreconciledProbe_loopFree
        satisfiableUnreconciledProbe_nonvariable hysupport hynone)
  have hfirst := hsatisfied.1 "x"
    (.expression [.symbol "f", .var "y"])
    (by simp [satisfiableUnreconciledProbe])
  have hsecond := hsatisfied.1 "x"
    (.expression [.symbol "f", .symbol "a"])
    (by simp [satisfiableUnreconciledProbe])
  have himpossible := hfirst.symm.trans hsecond
  simp [toLeaTTaAtom, applyClassSolution, hy] at himpossible

/-- Therefore the missing reconciliation-provenance hypothesis is also
strictly stronger than satisfiability: class coherence would force precisely
the canonical model refuted above. -/
theorem satisfiableUnreconciledProbe_not_classCoherent :
    ¬CanonicalClassCoherent satisfiableUnreconciledProbe
      satisfiableUnreconciledProbe_loopFree
      satisfiableUnreconciledProbe_nonvariable := by
  intro hcoherent
  apply satisfiableUnreconciledProbe_canonical_not_model
  exact canonicalValuation_satisfies_of_classCoherent
    satisfiableUnreconciledProbe_loopFree
    satisfiableUnreconciledProbe_nonvariable hcoherent

/-! A second canary separates successful *bare merge construction* from the
final matcher's loop filter.  Each input below is independently satisfiable,
and the spec merge fold can insert the fresh right assignment.  Their union
is nevertheless the finite equation `x = f(y), y = f(x)` and has no model. -/

def cyclicMergeLeft : Bindings :=
  Bindings.empty.assign "x" (.expression [.var "y"])

def cyclicMergeRight : Bindings :=
  Bindings.empty.assign "y" (.expression [.var "x"])

def cyclicMergeOut : Bindings :=
  cyclicMergeLeft.assign "y" (.expression [.var "x"])

/-- The left input of the cyclic merge has an explicit finite-term model. -/
theorem cyclicMergeLeft_has_model :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation cyclicMergeLeft := by
  let valuation : String → Metta.Atom := fun name =>
    if name = "x" then .expr [.var "y"] else .var name
  refine ⟨valuation, ?_⟩
  constructor
  · intro key value hassignment
    have hentry : key = "x" ∧ value = .expression [.var "y"] := by
      simpa [cyclicMergeLeft, Bindings.empty, Bindings.assign,
        Bindings.isBound, Bindings.lookup] using hassignment
    rcases hentry with ⟨rfl, rfl⟩
    simp [valuation, toLeaTTaAtom, applyClassSolution]
  · intro left right hequality
    simp [cyclicMergeLeft, Bindings.empty, Bindings.assign] at hequality

/-- The right input of the cyclic merge also has an explicit finite-term
model. -/
theorem cyclicMergeRight_has_model :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation cyclicMergeRight := by
  let valuation : String → Metta.Atom := fun name =>
    if name = "y" then .expr [.var "x"] else .var name
  refine ⟨valuation, ?_⟩
  constructor
  · intro key value hassignment
    have hentry : key = "y" ∧ value = .expression [.var "x"] := by
      simpa [cyclicMergeRight, Bindings.empty, Bindings.assign,
        Bindings.isBound, Bindings.lookup] using hassignment
    rcases hentry with ⟨rfl, rfl⟩
    simp [valuation, toLeaTTaAtom, applyClassSolution]
  · intro left right hequality
    simp [cyclicMergeRight, Bindings.empty, Bindings.assign] at hequality

/-- The bare relational merge really admits the cyclic union.  Consequently
`MergeRel` alone cannot carry a model-existence invariant. -/
theorem cyclicMerge_rel :
    Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic
      cyclicMergeLeft cyclicMergeRight cyclicMergeOut := by
  apply Spec.Match.Merge.MergeRel.mk
      (order := [.value "y" (.expression [.var "x"])])
  · change List.Perm
      [Spec.Match.Merge.Constraint.value "y" (.expression [.var "x"])]
      ([Spec.Match.Merge.Constraint.value "y"
        (.expression [.var "x"])]).eraseDups
    rw [show ([Spec.Match.Merge.Constraint.value "y"
        (.expression [.var "x"])]).eraseDups =
      [Spec.Match.Merge.Constraint.value "y"
        (.expression [.var "x"])] by decide]
  · apply Spec.Match.Merge.MergeConstraintsRel.value
    · apply Spec.Match.Merge.AddVarBindingRel.fresh
      simp [cyclicMergeLeft, Bindings.empty, Bindings.assign,
        Bindings.classValues, Bindings.eqClassOrdered,
        Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
        Bindings.eqStep, Bindings.lookup, Bindings.isBound]
    · exact .nil

/-- The cyclic merge result is not satisfiable: structural atom size would
have to be strictly larger in both directions. -/
theorem cyclicMergeOut_has_no_model :
    ¬∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation cyclicMergeOut := by
  rintro ⟨valuation, hsatisfied⟩
  have hx := hsatisfied.1 "x" (.expression [.var "y"]) (by
    simp [cyclicMergeOut, cyclicMergeLeft, Bindings.empty,
      Bindings.assign, Bindings.isBound, Bindings.lookup])
  have hy := hsatisfied.1 "y" (.expression [.var "x"]) (by
    simp [cyclicMergeOut, cyclicMergeLeft, Bindings.empty,
      Bindings.assign, Bindings.isBound, Bindings.lookup])
  have hxSize := congrArg Metta.Atom.size hx
  have hySize := congrArg Metta.Atom.size hy
  simp [toLeaTTaAtom, applyClassSolution, Metta.Atom.size] at hxSize hySize
  omega

/-- The same probe confirms exactly why the outer spec matcher carries its
semantic loop filter. -/
theorem cyclicMergeOut_not_loopFree :
    ¬Spec.Match.Merge.SemanticLoopFree cyclicMergeOut := by
  intro hloopFree
  have hxy : Spec.Match.Merge.ClassDepends
      cyclicMergeOut "x" "y" := by
    refine ⟨"x", .expression [.var "y"], "y", ?_, ?_, ?_, ?_, ?_⟩
    · simp [cyclicMergeOut, cyclicMergeLeft, Bindings.empty,
        Bindings.assign, Bindings.isBound, Bindings.lookup]
    · simp [cyclicMergeOut, cyclicMergeLeft, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.empty,
        Bindings.assign, Bindings.isBound, Bindings.lookup]
    · exact .expression (by simp) (.var "y")
    · simp [cyclicMergeOut, cyclicMergeLeft, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.empty,
        Bindings.assign, Bindings.isBound, Bindings.lookup]
    · simp
  have hyx : Spec.Match.Merge.ClassDepends
      cyclicMergeOut "y" "x" := by
    refine ⟨"y", .expression [.var "x"], "x", ?_, ?_, ?_, ?_, ?_⟩
    · simp [cyclicMergeOut, cyclicMergeLeft, Bindings.empty,
        Bindings.assign, Bindings.isBound, Bindings.lookup]
    · simp [cyclicMergeOut, cyclicMergeLeft, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.empty,
        Bindings.assign, Bindings.isBound, Bindings.lookup]
    · exact .expression (by simp) (.var "x")
    · simp [cyclicMergeOut, cyclicMergeLeft, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.empty,
        Bindings.assign, Bindings.isBound, Bindings.lookup]
    · simp
  exact hloopFree "x" (.tail (.single hxy) hyx)

end Mettapedia.Languages.MeTTa.HE.Spec.Match.ModelTheory
