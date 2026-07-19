import Mettapedia.Languages.MeTTa.HE.HumanMatchModelTheory

/-!
# Structural reconciliation certificate for the human matcher

This file isolates the representation-independent certificate needed by the
canonical human binding model.  Two atoms are structurally solved by a binding
record when equal constructors agree pointwise and every variable discrepancy
is justified either by equality-class closure or by a value stored in that
class.  No binding-list order, equality-edge orientation, representative
chronology, unification fuel, or executable matcher occurs in the judgment.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanMatchStructuralModel

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open HumanMatchModelTheory

mutual

/-- Structural equality after reading equality classes and their stored
values.  The two assignment constructors are the variable/non-variable leaves
created by recursive reconciliation. -/
inductive AtomSolved (bindings : Bindings) : Atom → Atom → Prop where
  | symbol (name : String) :
      AtomSolved bindings (.symbol name) (.symbol name)
  | varVar {left right : String} :
      right ∈ bindings.eqClass left →
      AtomSolved bindings (.var left) (.var right)
  | assignedLeft {left key : String} {right : Atom} :
      (key, right) ∈ bindings.assignments →
      key ∈ bindings.eqClass left →
      AtomSolved bindings (.var left) right
  | assignedRight {left : Atom} {key right : String} :
      (key, left) ∈ bindings.assignments →
      key ∈ bindings.eqClass right →
      AtomSolved bindings left (.var right)
  | aliasLeft {left key : String} {right : Atom} :
      key ∈ bindings.eqClass left →
      AtomSolved bindings (.var key) right →
      AtomSolved bindings (.var left) right
  | aliasRight {left : Atom} {key right : String} :
      key ∈ bindings.eqClass right →
      AtomSolved bindings left (.var key) →
      AtomSolved bindings left (.var right)
  | grounded (value : GroundedValue) :
      AtomSolved bindings (.grounded value) (.grounded value)
  | expression {left right : List Atom} :
      AtomsSolved bindings left right →
      AtomSolved bindings (.expression left) (.expression right)

/-- List companion of `AtomSolved`. -/
inductive AtomsSolved (bindings : Bindings) :
    List Atom → List Atom → Prop where
  | nil : AtomsSolved bindings [] []
  | cons {left right : Atom} {lefts rights : List Atom} :
      AtomSolved bindings left right →
      AtomsSolved bindings lefts rights →
      AtomsSolved bindings (left :: lefts) (right :: rights)

end

mutual

/-- Directional reconciliation after recursively reading stored class values.
Unlike `AtomSolved`, assignment leaves may continue by comparing the stored
value with the proposed atom.  There is deliberately no generic transitivity
constructor: every change of head atom must be justified by syntax, an
equality class, or one concrete stored assignment. -/
inductive AtomReconciled (bindings : Bindings) : Atom → Atom → Prop where
  | symbol (name : String) :
      AtomReconciled bindings (.symbol name) (.symbol name)
  | varVar {left right : String} :
      right ∈ bindings.eqClass left →
      AtomReconciled bindings (.var left) (.var right)
  | assignedLeft {left key : String} {stored right : Atom} :
      (key, stored) ∈ bindings.assignments →
      key ∈ bindings.eqClass left →
      AtomReconciled bindings stored right →
      AtomReconciled bindings (.var left) right
  | assignedRight {left stored : Atom} {key right : String} :
      (key, stored) ∈ bindings.assignments →
      key ∈ bindings.eqClass right →
      AtomReconciled bindings left stored →
      AtomReconciled bindings left (.var right)
  | grounded (value : GroundedValue) :
      AtomReconciled bindings (.grounded value) (.grounded value)
  | expression {left right : List Atom} :
      AtomsReconciled bindings left right →
      AtomReconciled bindings (.expression left) (.expression right)

/-- List companion of `AtomReconciled`. -/
inductive AtomsReconciled (bindings : Bindings) :
    List Atom → List Atom → Prop where
  | nil : AtomsReconciled bindings [] []
  | cons {left right : Atom} {lefts rights : List Atom} :
      AtomReconciled bindings left right →
      AtomsReconciled bindings lefts rights →
      AtomsReconciled bindings (left :: lefts) (right :: rights)

end

/-- Paired elimination principle for directional reconciliation. -/
theorem reconciled_mutual_induction
    {bindings : Bindings}
    {atomMotive : ∀ left right,
      AtomReconciled bindings left right → Prop}
    {atomsMotive : ∀ left right,
      AtomsReconciled bindings left right → Prop}
    (symbol : ∀ name,
      atomMotive (.symbol name) (.symbol name) (.symbol name))
    (varVar : ∀ {left right} (hclass : right ∈ bindings.eqClass left),
      atomMotive (.var left) (.var right) (.varVar hclass))
    (assignedLeft : ∀ {left key stored right}
      (hassignment : (key, stored) ∈ bindings.assignments)
      (hclass : key ∈ bindings.eqClass left)
      (htail : AtomReconciled bindings stored right),
      atomMotive stored right htail →
        atomMotive (.var left) right
          (.assignedLeft hassignment hclass htail))
    (assignedRight : ∀ {left stored key right}
      (hassignment : (key, stored) ∈ bindings.assignments)
      (hclass : key ∈ bindings.eqClass right)
      (htail : AtomReconciled bindings left stored),
      atomMotive left stored htail →
        atomMotive left (.var right)
          (.assignedRight hassignment hclass htail))
    (grounded : ∀ value,
      atomMotive (.grounded value) (.grounded value) (.grounded value))
    (expression : ∀ {left right}
      (hitems : AtomsReconciled bindings left right),
      atomsMotive left right hitems →
        atomMotive (.expression left) (.expression right)
          (.expression hitems))
    (nil : atomsMotive [] [] .nil)
    (cons : ∀ {left right lefts rights}
      (hhead : AtomReconciled bindings left right)
      (htail : AtomsReconciled bindings lefts rights),
      atomMotive left right hhead →
      atomsMotive lefts rights htail →
        atomsMotive (left :: lefts) (right :: rights)
          (.cons hhead htail)) :
    (∀ left right (hreconciled : AtomReconciled bindings left right),
      atomMotive left right hreconciled) ∧
    (∀ left right (hreconciled : AtomsReconciled bindings left right),
      atomsMotive left right hreconciled) :=
  ⟨fun _ _ hreconciled => AtomReconciled.rec symbol varVar
      assignedLeft assignedRight grounded expression nil cons hreconciled,
    fun _ _ hreconciled => AtomsReconciled.rec symbol varVar
      assignedLeft assignedRight grounded expression nil cons hreconciled⟩

/-- Paired elimination principle for the mutually inductive structural-solution
judgments.  Lean exposes the two generated recursors separately; packaging
them once avoids defining recursive proof functions over proof-irrelevant
arguments. -/
theorem solved_mutual_induction
    {bindings : Bindings}
    {atomMotive : ∀ left right,
      AtomSolved bindings left right → Prop}
    {atomsMotive : ∀ left right,
      AtomsSolved bindings left right → Prop}
    (symbol : ∀ name,
      atomMotive (.symbol name) (.symbol name) (.symbol name))
    (varVar : ∀ {left right} (hclass : right ∈ bindings.eqClass left),
      atomMotive (.var left) (.var right) (.varVar hclass))
    (assignedLeft : ∀ {left key right}
      (hassignment : (key, right) ∈ bindings.assignments)
      (hclass : key ∈ bindings.eqClass left),
      atomMotive (.var left) right (.assignedLeft hassignment hclass))
    (assignedRight : ∀ {left key right}
      (hassignment : (key, left) ∈ bindings.assignments)
      (hclass : key ∈ bindings.eqClass right),
      atomMotive left (.var right) (.assignedRight hassignment hclass))
    (aliasLeft : ∀ {left key right}
      (hclass : key ∈ bindings.eqClass left)
      (htail : AtomSolved bindings (.var key) right),
      atomMotive (.var key) right htail →
        atomMotive (.var left) right (.aliasLeft hclass htail))
    (aliasRight : ∀ {left key right}
      (hclass : key ∈ bindings.eqClass right)
      (htail : AtomSolved bindings left (.var key)),
      atomMotive left (.var key) htail →
        atomMotive left (.var right) (.aliasRight hclass htail))
    (grounded : ∀ value,
      atomMotive (.grounded value) (.grounded value) (.grounded value))
    (expression : ∀ {left right}
      (hitems : AtomsSolved bindings left right),
      atomsMotive left right hitems →
        atomMotive (.expression left) (.expression right)
          (.expression hitems))
    (nil : atomsMotive [] [] .nil)
    (cons : ∀ {left right lefts rights}
      (hhead : AtomSolved bindings left right)
      (htail : AtomsSolved bindings lefts rights),
      atomMotive left right hhead →
      atomsMotive lefts rights htail →
        atomsMotive (left :: lefts) (right :: rights)
          (.cons hhead htail)) :
    (∀ left right (hsolved : AtomSolved bindings left right),
      atomMotive left right hsolved) ∧
    (∀ left right (hsolved : AtomsSolved bindings left right),
      atomsMotive left right hsolved) :=
  ⟨fun _ _ hsolved => AtomSolved.rec symbol varVar assignedLeft
      assignedRight aliasLeft aliasRight grounded expression nil cons hsolved,
    fun _ _ hsolved => AtomsSolved.rec symbol varVar assignedLeft
      assignedRight aliasLeft aliasRight grounded expression nil cons hsolved⟩

/-- Every pair of raw assignments whose keys lie in one equality class has a
structural solution in the same record.  This sees all constraints rather
than the chronology-sensitive lookup projection used by `classValues`. -/
def ClassAssignmentsStructurallySolved (bindings : Bindings) : Prop :=
  ∀ {leftKey rightKey : String} {leftValue rightValue : Atom},
    (leftKey, leftValue) ∈ bindings.assignments →
    (rightKey, rightValue) ∈ bindings.assignments →
    rightKey ∈ bindings.eqClass leftKey →
      AtomSolved bindings leftValue rightValue

/-- Every pair of values stored in one source equality class has a common
source assignment whose two structural equations are solved in `target`.
Separating target from source lets a later reconciliation step certify an
earlier accumulator without requiring literal assignment-list inclusion. -/
def ClassAssignmentsStructurallyRootedIn
    (target source : Bindings) : Prop :=
  ∀ {leftKey rightKey : String} {leftValue rightValue : Atom},
    (leftKey, leftValue) ∈ source.assignments →
    (rightKey, rightValue) ∈ source.assignments →
    rightKey ∈ source.eqClass leftKey →
      ∃ pivotKey pivotValue,
        (pivotKey, pivotValue) ∈ source.assignments ∧
        pivotKey ∈ source.eqClass leftKey ∧
        AtomSolved target pivotValue leftValue ∧
        AtomSolved target pivotValue rightValue

/-- Every pair of values stored in one equality class has a common stored
structural root.  This is the certificate produced by reconciliation: the
human rules choose one class value and recursively match it against all the
others.  Keeping the common root explicit is weaker than demanding a
syntactic transitivity rule for `AtomSolved`, and therefore does not make an
unreconciled class such as `{x ↦ a, y ↦ b, x = y}` coherent by fiat. -/
def ClassAssignmentsStructurallyRooted (bindings : Bindings) : Prop :=
  ClassAssignmentsStructurallyRootedIn bindings bindings

/-- Every pair of source values in one class shares a source pivot whose two
directional recursive equations are realized in `target`. -/
def ClassAssignmentsReconciledIn
    (target source : Bindings) : Prop :=
  ∀ {leftKey rightKey : String} {leftValue rightValue : Atom},
    (leftKey, leftValue) ∈ source.assignments →
    (rightKey, rightValue) ∈ source.assignments →
    rightKey ∈ source.eqClass leftKey →
      ∃ pivotKey pivotValue,
        (pivotKey, pivotValue) ∈ source.assignments ∧
        pivotKey ∈ source.eqClass leftKey ∧
        AtomReconciled target pivotValue leftValue ∧
        AtomReconciled target pivotValue rightValue

/-- Final reconciliation certificate used by the model theorem.  This admits
nested solved assignments while retaining the explicit common-root
provenance that rules out incompatible acyclic classes. -/
def ClassAssignmentsReconciled (bindings : Bindings) : Prop :=
  ClassAssignmentsReconciledIn bindings bindings

/-- A variable class is visible under an atom when some syntactically
occurring variable belongs to that equality class. -/
def AtomClassOccurs (bindings : Bindings) (atom : Atom)
    (name : String) : Prop :=
  ∃ occurrence,
    HumanMatchMergeSpec.AtomOccurs atom occurrence ∧
      name ∈ bindings.eqClass occurrence

/-- Every variable occurring in an atom belongs to a dependency class that is
strictly below `source`.  This is the semantic guard that makes recursive
assignment dereferencing safe: an unreconciled route through the current
class cannot masquerade as a smaller recursive solution. -/
def AtomDependenciesBelow
    (bindings : Bindings) (source : DependencyNode bindings)
    (atom : Atom) : Prop :=
  ∀ name, HumanMatchMergeSpec.AtomOccurs atom name →
    ∃ hsupport : name ∈ bindingSupport bindings,
      DependencyOrder bindings
        (representativeNode ⟨name, hsupport⟩) source

/-- A dependency edge is insensitive to which name denotes its source
equality class. -/
theorem classDepends_of_source_mem_eqClass
    {bindings : Bindings} {source replacement target : String}
    (hclass : replacement ∈ bindings.eqClass source)
    (hdepends : HumanMatchMergeSpec.ClassDepends bindings source target) :
    HumanMatchMergeSpec.ClassDepends bindings replacement target := by
  rcases hdepends with
    ⟨key, value, dependency, hassignment, hsource, hoccurs,
      htarget, hproper⟩
  refine ⟨key, value, dependency, hassignment, ?_, hoccurs,
    htarget, hproper⟩
  rw [EqualityClosure.mem_eqClass_iff_reachable]
    at hsource hclass ⊢
  exact hsource.trans hclass

/-- Strict dependency order is likewise invariant under changing the source
name within its equality class. -/
theorem dependencyOrder_of_source_mem_eqClass
    {bindings : Bindings} {target source replacement : DependencyNode bindings}
    (hclass : replacement.1 ∈ bindings.eqClass source.1)
    (hlt : DependencyOrder bindings target source) :
    DependencyOrder bindings target replacement := by
  change Relation.TransGen
      (HumanMatchMergeSpec.ClassDepends bindings) source.1 target.1 at hlt
  change Relation.TransGen
      (HumanMatchMergeSpec.ClassDepends bindings) replacement.1 target.1
  let motive := fun start
      (_ : Relation.TransGen
        (HumanMatchMergeSpec.ClassDepends bindings) start target.1) =>
      ∀ replacement,
        replacement ∈ bindings.eqClass start →
        Relation.TransGen
          (HumanMatchMergeSpec.ClassDepends bindings)
          replacement target.1
  exact Relation.TransGen.head_induction_on
    (motive := motive) hlt
    (fun hstep replacement hreplacement =>
      .single
        (classDepends_of_source_mem_eqClass hreplacement hstep))
    (fun hstep htail _ih replacement hreplacement =>
      htail.head
        (classDepends_of_source_mem_eqClass hreplacement hstep))
    replacement.1 hclass

/-- An atom remains strictly below the ambient class when that class is named
by another connected variable. -/
theorem AtomDependenciesBelow.of_source_mem_eqClass
    {bindings : Bindings} {source replacement : DependencyNode bindings}
    {atom : Atom}
    (hbelow : AtomDependenciesBelow bindings source atom)
    (hclass : replacement.1 ∈ bindings.eqClass source.1) :
    AtomDependenciesBelow bindings replacement atom := by
  intro name hoccurs
  obtain ⟨hsupport, hlt⟩ := hbelow name hoccurs
  exact ⟨hsupport, dependencyOrder_of_source_mem_eqClass hclass hlt⟩

/-- The variables in a stored assignment value lie below any node above the
assignment's own class. -/
theorem ClassAssignment.value_dependenciesBelow
    {bindings : Bindings}
    (hnonvariable : AssignmentsNonVariable bindings)
    {source target : DependencyNode bindings}
    (hlt : DependencyOrder bindings target source)
    (assignment : ClassAssignment bindings target.1) :
    AtomDependenciesBelow bindings source assignment.1.2 := by
  intro name hoccurs
  let hsupport := assignment_value_var_mem_bindingSupport
    assignment.2.1 hoccurs
  refine ⟨hsupport, ?_⟩
  have hchild := chosenDependencyNode_lt
    assignment hnonvariable hoccurs
  have hnode : representativeNode
        (bindings := bindings) ⟨name, hsupport⟩ =
      chosenDependencyNode assignment hoccurs := by
    apply Subtype.ext
    rfl
  rw [hnode]
  exact Relation.TransGen.trans hlt hchild

/-- In particular, every variable in a class assignment is a direct smaller
dependency of that class. -/
theorem ClassAssignment.value_dependenciesBelow_source
    {bindings : Bindings}
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (assignment : ClassAssignment bindings source.1) :
    AtomDependenciesBelow bindings source assignment.1.2 := by
  intro name hoccurs
  let hsupport := assignment_value_var_mem_bindingSupport
    assignment.2.1 hoccurs
  refine ⟨hsupport, ?_⟩
  have hchild := chosenDependencyNode_lt
    assignment hnonvariable hoccurs
  have hnode : representativeNode
        (bindings := bindings) ⟨name, hsupport⟩ =
      chosenDependencyNode assignment hoccurs := by
    apply Subtype.ext
    rfl
  simpa [hnode] using hchild

/-- If a variable occurs below an ambient class, every value stored in that
variable's equality class is below the same ambient class.  This is the scoped
guard used when a recursive merge discovers an older class value while
realizing an equation. -/
theorem ClassAssignment.value_dependenciesBelow_of_atomOccurs
    {bindings : Bindings}
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings} {atom : Atom} {name : String}
    (hbelow : AtomDependenciesBelow bindings source atom)
    (hoccurs : HumanMatchMergeSpec.AtomOccurs atom name)
    (assignment : ClassAssignment bindings name) :
    AtomDependenciesBelow bindings source assignment.1.2 := by
  obtain ⟨hnameSupport, hlt⟩ := hbelow name hoccurs
  let target : DependencyNode bindings :=
    representativeNode ⟨name, hnameSupport⟩
  have hnameTarget : name ∈ bindings.eqClass target.1 := by
    change name ∈ bindings.eqClass (bindings.eqRepresentative name)
    exact mem_eqClass_symm
      (eqRepresentative_mem_eqClass bindings name)
  have hassignmentClass := assignment.2.2
  have hkeyTarget : assignment.1.1 ∈ bindings.eqClass target.1 := by
    rw [EqualityClosure.mem_eqClass_iff_reachable]
      at hnameTarget hassignmentClass ⊢
    exact hnameTarget.trans hassignmentClass
  let targetAssignment : ClassAssignment bindings target.1 :=
    ⟨assignment.1, assignment.2.1, hkeyTarget⟩
  exact ClassAssignment.value_dependenciesBelow
    hnonvariable hlt targetAssignment

/-! ## Strict dependency scope of transient bindings

Recursive reconciliation is semantically safe below an ambient dependency
class even when its transient binding record is not retained literally in the
eventual output.  The scope below records exactly the information needed for
that argument: both sides of every transient constraint mention only classes
strictly below the ambient class.  It is deliberately stated relative to the
eventual target, so no chronology-sensitive transport of dependency orders is
required.
-/

/-- Every atom in a list lies strictly below one ambient dependency class. -/
def AtomsDependenciesBelow (target : Bindings)
    (source : DependencyNode target) (atoms : List Atom) : Prop :=
  ∀ atom ∈ atoms, AtomDependenciesBelow target source atom

/-- Both endpoints of one neutral constraint lie strictly below an ambient
dependency class. -/
def ConstraintDependenciesBelow (target : Bindings)
    (source : DependencyNode target) :
    HumanMatchMergeSpec.Constraint → Prop
  | .value key value =>
      AtomDependenciesBelow target source (.var key) ∧
        AtomDependenciesBelow target source value
  | .equality left right =>
      AtomDependenciesBelow target source (.var left) ∧
        AtomDependenciesBelow target source (.var right)

/-- Every constraint in a concrete fold order lies below the ambient class. -/
def ConstraintsDependenciesBelow (target : Bindings)
    (source : DependencyNode target)
    (constraints : List HumanMatchMergeSpec.Constraint) : Prop :=
  ∀ constraint ∈ constraints,
    ConstraintDependenciesBelow target source constraint

/-- Representation-independent strict dependency scope of a binding record. -/
structure BindingDependenciesBelow (target : Bindings)
    (source : DependencyNode target) (bindings : Bindings) : Prop where
  assignments : ∀ key value,
    (key, value) ∈ bindings.assignments →
      AtomDependenciesBelow target source (.var key) ∧
        AtomDependenciesBelow target source value
  equalities : ∀ left right,
    (left, right) ∈ bindings.equalities →
      AtomDependenciesBelow target source (.var left) ∧
        AtomDependenciesBelow target source (.var right)

/-- Empty bindings contain no out-of-scope constraint. -/
theorem BindingDependenciesBelow.empty
    (target : Bindings) (source : DependencyNode target) :
    BindingDependenciesBelow target source Bindings.empty where
  assignments _ _ hmem := by simp [Bindings.empty] at hmem
  equalities _ _ hmem := by simp [Bindings.empty] at hmem

/-- Restricting the represented binding record preserves strict scope. -/
theorem BindingDependenciesBelow.of_subrecord
    {target sourceBindings before : Bindings}
    {source : DependencyNode target}
    (hscope : BindingDependenciesBelow target source sourceBindings)
    (hsubrecord : BindingSubrecord before sourceBindings) :
    BindingDependenciesBelow target source before where
  assignments key value hmem :=
    hscope.assignments key value (hsubrecord.1 _ hmem)
  equalities left right hmem :=
    hscope.equalities left right (hsubrecord.2 _ hmem)

/-- Adding a fresh value constraint preserves scope when both endpoints are
already known to be below the ambient class. -/
theorem BindingDependenciesBelow.assign
    {target bindings : Bindings} {source : DependencyNode target}
    {key : String} {value : Atom}
    (hscope : BindingDependenciesBelow target source bindings)
    (hkey : AtomDependenciesBelow target source (.var key))
    (hvalue : AtomDependenciesBelow target source value) :
    BindingDependenciesBelow target source (bindings.assign key value) := by
  constructor
  · intro storedKey storedValue hmem
    by_cases hbound : bindings.isBound key
    · simp only [Bindings.assign, hbound, if_pos] at hmem
      rcases List.mem_map.mp hmem with
        ⟨⟨oldKey, oldValue⟩, hold, hmapped⟩
      by_cases hkeyEq : oldKey = key
      · subst oldKey
        simp at hmapped
        rcases hmapped with ⟨rfl, rfl⟩
        exact ⟨hkey, hvalue⟩
      · simp [hkeyEq] at hmapped
        rcases hmapped with ⟨rfl, rfl⟩
        exact hscope.assignments oldKey oldValue hold
    · have hcases :
          (storedKey, storedValue) ∈ bindings.assignments ∨
            (storedKey = key ∧ storedValue = value) := by
        simpa [Bindings.assign, hbound] using hmem
      rcases hcases with hold | hnew
      · exact hscope.assignments storedKey storedValue hold
      · rcases hnew with ⟨rfl, rfl⟩
        exact ⟨hkey, hvalue⟩
  · intro left right hmem
    simpa [Bindings.assign] using hscope.equalities left right hmem

/-- Adding one equality edge preserves old scope and records the two scoped
endpoints of the new edge. -/
theorem BindingDependenciesBelow.addEquality
    {target bindings : Bindings} {source : DependencyNode target}
    {left right : String}
    (hscope : BindingDependenciesBelow target source bindings)
    (hleft : AtomDependenciesBelow target source (.var left))
    (hright : AtomDependenciesBelow target source (.var right)) :
    BindingDependenciesBelow target source
      (bindings.addEquality left right) := by
  constructor
  · intro key value hmem
    exact hscope.assignments key value (by
      simpa [Bindings.addEquality] using hmem)
  · intro storedLeft storedRight hmem
    have hcases : (storedLeft, storedRight) ∈ bindings.equalities ∨
        (storedLeft = left ∧ storedRight = right) := by
      simpa [Bindings.addEquality] using hmem
    rcases hcases with hold | hnew
    · exact hscope.equalities storedLeft storedRight hold
    · rcases hnew with ⟨rfl, rfl⟩
      exact ⟨hleft, hright⟩

/-- Every visible class value inherits the strict scope of the assignment
record that stores it. -/
private theorem lookup_mem_of_eq_some_scoped {key : String} {value : Atom} :
    ∀ {assignments : List (String × Atom)},
      List.lookup key assignments = some value →
      (key, value) ∈ assignments
  | [], hlookup => by simp at hlookup
  | (storedKey, storedValue) :: assignments, hlookup => by
      by_cases hkey : key = storedKey
      · subst storedKey
        simp only [List.lookup, BEq.beq, decide_true] at hlookup
        cases hlookup
        simp
      · have hne : (key == storedKey) = false := by
          simpa [BEq.beq, decide_eq_false_iff_not] using hkey
        simp only [List.lookup, hne] at hlookup
        exact List.mem_cons_of_mem _
          (lookup_mem_of_eq_some_scoped hlookup)

theorem BindingDependenciesBelow.value_of_mem_classValues
    {target bindings : Bindings} {source : DependencyNode target}
    (hscope : BindingDependenciesBelow target source bindings)
    {key : String} {value : Atom}
    (hvalue : value ∈ bindings.classValues key) :
    AtomDependenciesBelow target source value := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with
    ⟨storedKey, _hclass, hlookup⟩
  exact (hscope.assignments storedKey value
    (lookup_mem_of_eq_some_scoped hlookup)).2

/-- The human match/merge derivation never invents an out-of-scope variable.
The theorem is simultaneous across all six relations because reconciliation
feeds recursively matched constraints back through the live merge. -/
theorem humanMatch_dependenciesBelow
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out) :
    ∀ {target : Bindings} {source : DependencyNode target},
      AtomDependenciesBelow target source query →
      AtomDependenciesBelow target source pattern →
        BindingDependenciesBelow target source out := by
  intro target source hquery hpattern
  refine (HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun left right result _ =>
      ∀ {target : Bindings} {source : DependencyNode target},
        AtomDependenciesBelow target source left →
        AtomDependenciesBelow target source right →
          BindingDependenciesBelow target source result)
    (motive_2 := fun left right seed result _ =>
      ∀ {target : Bindings} {source : DependencyNode target},
        AtomsDependenciesBelow target source left →
        AtomsDependenciesBelow target source right →
        BindingDependenciesBelow target source seed →
          BindingDependenciesBelow target source result)
    (motive_3 := fun seed varName value result _ =>
      ∀ {target : Bindings} {source : DependencyNode target},
        BindingDependenciesBelow target source seed →
        AtomDependenciesBelow target source (.var varName) →
        AtomDependenciesBelow target source value →
          BindingDependenciesBelow target source result)
    (motive_4 := fun seed left right result _ =>
      ∀ {target : Bindings} {source : DependencyNode target},
        BindingDependenciesBelow target source seed →
        AtomDependenciesBelow target source (.var left) →
        AtomDependenciesBelow target source (.var right) →
          BindingDependenciesBelow target source result)
    (motive_5 := fun seed constraints result _ =>
      ∀ {target : Bindings} {source : DependencyNode target},
        BindingDependenciesBelow target source seed →
        ConstraintsDependenciesBelow target source constraints →
          BindingDependenciesBelow target source result)
    (motive_6 := fun left right result _ =>
      ∀ {target : Bindings} {source : DependencyNode target},
        BindingDependenciesBelow target source left →
        BindingDependenciesBelow target source right →
          BindingDependenciesBelow target source result)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (t := hmatch)) hquery hpattern
  next =>
      intro symbol hadmissible target source hleft hright
      exact BindingDependenciesBelow.empty target source
  next =>
      intro left right hadmissible target source hleft hright
      exact (BindingDependenciesBelow.empty target source).addEquality
        hleft hright
  next =>
      intro varName value hnonvar hadmissible target source hleft hright
      exact (BindingDependenciesBelow.empty target source).assign hleft hright
  next =>
      intro value varName hnonvar hadmissible target source hleft hright
      exact (BindingDependenciesBelow.empty target source).assign hright hleft
  next =>
      intro left right result hitems hadmissible ih
        target source hleft hright
      apply ih
      · intro atom hmem name hoccurs
        exact hleft name (.expression hmem hoccurs)
      · intro atom hmem name hoccurs
        exact hright name (.expression hmem hoccurs)
      · exact BindingDependenciesBelow.empty target source
  next =>
      intro grounded right result hright hcustom hground hadmissible
        target source hleftBelow hrightBelow
      rcases hground with ⟨hrightEq, houtEq⟩
      subst right
      subst result
      exact BindingDependenciesBelow.empty target source
  next =>
      intro left grounded result hleft hleftNoCustom hcustom hground
        hadmissible target source hleftBelow hrightBelow
      rcases hground with ⟨hleftEq, houtEq⟩
      subst left
      subst result
      exact BindingDependenciesBelow.empty target source
  next =>
      intro left right hleft hright hadmissible
      exact (hleft (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim
  next =>
      intro seed target source hleft hright hseed
      exact hseed
  next =>
      intro left right lefts rights seed matched next result
        hhead hmerge htail ihHead ihMerge ihTail
        target source hlefts hrights hseed
      have hleft : AtomDependenciesBelow target source left :=
        hlefts left (by simp)
      have hright : AtomDependenciesBelow target source right :=
        hrights right (by simp)
      have hmatched := ihHead hleft hright
      have hnext := ihMerge hseed hmatched
      apply ihTail
      · intro atom hmem
        exact hlefts atom (by simp [hmem])
      · intro atom hmem
        exact hrights atom (by simp [hmem])
      · exact hnext
  next =>
      intro seed varName value hvalues target source hseed hkey hvalue
      exact hseed.assign hkey hvalue
  next =>
      intro seed varName value first rest hvalues hagree hvalueEq
        target source hseed hkey hvalue
      exact hseed
  next =>
      intro seed varName value first rest matched result hvalues hagree
        hne hhead hmerge ihHead ihMerge
        target source hseed hkey hvalue
      have hfirst : AtomDependenciesBelow target source first := by
        apply hseed.value_of_mem_classValues
        exact (List.Perm.mem_iff hvalues).mp (by simp)
      exact ihMerge hseed (ihHead hfirst hvalue)
  next =>
      intro seed varName value first rest matched result hvalues hnotAgree
        hlist hmerge ihList ihMerge
        target source hseed hkey hvalue
      have hall : ∀ candidate ∈ first :: rest,
          AtomDependenciesBelow target source candidate := by
        intro candidate hmem
        apply hseed.value_of_mem_classValues
        exact (List.Perm.mem_iff hvalues).mp hmem
      have hmatched := ihList
        (by
          intro candidate hmem
          rcases List.mem_replicate.mp hmem with ⟨_, hcandidate⟩
          subst candidate
          exact hall first (by simp))
        (by
          intro candidate hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hrest | rfl
          · exact hall candidate (by simp [hrest])
          · exact hvalue)
        (BindingDependenciesBelow.empty target source)
      exact ihMerge hseed hmatched
  next =>
      intro seed left right values hvalues hagree
        target source hseed hleft hright
      exact hseed.addEquality hleft hright
  next =>
      intro seed left right first rest matched result hvalues hnotAgree
        hlist hmerge ihList ihMerge
        target source hseed hleft hright
      have hcandidate := hseed.addEquality hleft hright
      have hall : ∀ candidate ∈ first :: rest,
          AtomDependenciesBelow target source candidate := by
        intro candidate hmem
        apply hcandidate.value_of_mem_classValues
        exact (List.Perm.mem_iff hvalues).mp hmem
      have hmatched := ihList
        (by
          intro candidate hmem
          rcases List.mem_replicate.mp hmem with ⟨_, hcandidate⟩
          subst candidate
          exact hall first (by simp))
        (by
          intro candidate hmem
          exact hall candidate (by simp [hmem]))
        (BindingDependenciesBelow.empty target source)
      exact ihMerge hcandidate hmatched
  next =>
      intro seed target source hseed hconstraints
      exact hseed
  next =>
      intro seed next result varName value rest hadd htail ihAdd ihTail
        target source hseed hconstraints
      have hhead := hconstraints (.value varName value) (by simp)
      apply ihTail
      · exact ihAdd hseed hhead.1 hhead.2
      · intro constraint hmem
        exact hconstraints constraint (by simp [hmem])
  next =>
      intro seed next result left right rest hadd htail ihAdd ihTail
        target source hseed hconstraints
      have hhead := hconstraints (.equality left right) (by simp)
      apply ihTail
      · exact ihAdd hseed hhead.1 hhead.2
      · intro constraint hmem
        exact hconstraints constraint (by simp [hmem])
  next =>
      intro left right result order horder hfold ihFold
        target source hleft hright
      apply ihFold hleft
      intro constraint hmem
      have hrightMem : constraint ∈ HumanMatchMergeSpec.constraints right :=
        (List.Perm.mem_iff horder).mp hmem
      cases constraint with
      | value key value =>
          exact hright.assignments key value
            (HumanMatchSolutionTheory.value_mem_constraints_iff.mp hrightMem)
      | equality edgeLeft edgeRight =>
          exact hright.equalities edgeLeft edgeRight
            (HumanMatchSolutionTheory.equality_mem_constraints_iff.mp hrightMem)

private theorem solved_sound_pair
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings) :
    (∀ left right (_ : AtomSolved bindings left right),
      applyClassSolution valuation (toLeaTTaAtom left) =
        applyClassSolution valuation (toLeaTTaAtom right)) ∧
    (∀ left right (_ : AtomsSolved bindings left right),
      (toLeaTTaAtoms left).map (applyClassSolution valuation) =
        (toLeaTTaAtoms right).map (applyClassSolution valuation)) := by
  apply solved_mutual_induction
  · intro name
    rfl
  · intro left right hclass
    simpa [toLeaTTaAtom, applyClassSolution] using
      hsatisfied.eq_of_mem_eqClass hclass
  · intro left key right hassignment hclass
    simpa [toLeaTTaAtom, applyClassSolution] using
      (hsatisfied.eq_of_mem_eqClass hclass).trans
        (hsatisfied.1 _ _ hassignment)
  · intro left key right hassignment hclass
    simpa [toLeaTTaAtom, applyClassSolution] using
      ((hsatisfied.eq_of_mem_eqClass hclass).trans
        (hsatisfied.1 _ _ hassignment)).symm
  · intro left key right hclass htail ih
    have htailEq' : valuation key =
        applyClassSolution valuation (toLeaTTaAtom right) := by
      simpa [toLeaTTaAtom, applyClassSolution] using ih
    simpa [toLeaTTaAtom, applyClassSolution] using
      (hsatisfied.eq_of_mem_eqClass hclass).trans htailEq'
  · intro left key right hclass htail ih
    have htailEq' :
        applyClassSolution valuation (toLeaTTaAtom left) = valuation key := by
      simpa [toLeaTTaAtom, applyClassSolution] using ih
    simpa [toLeaTTaAtom, applyClassSolution] using
      htailEq'.trans (hsatisfied.eq_of_mem_eqClass hclass).symm
  · intro value
    rfl
  · intro left right hitems ih
    simp only [toLeaTTaAtom, applyClassSolution]
    congr 1
  · rfl
  · intro left right lefts rights hhead htail ihHead ihTail
    simp only [toLeaTTaAtoms, List.map_cons, List.cons.injEq]
    exact ⟨ihHead, ihTail⟩

/-- Every structural solution is a semantic consequence of the binding
record. -/
theorem AtomSolved.sound
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    {left right : Atom}
    (hsolved : AtomSolved bindings left right) :
    applyClassSolution valuation (toLeaTTaAtom left) =
      applyClassSolution valuation (toLeaTTaAtom right) :=
  (solved_sound_pair hsatisfied).1 left right hsolved

/-- List companion of `AtomSolved.sound`. -/
theorem AtomsSolved.sound
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    {left right : List Atom}
    (hsolved : AtomsSolved bindings left right) :
    (toLeaTTaAtoms left).map (applyClassSolution valuation) =
      (toLeaTTaAtoms right).map (applyClassSolution valuation) :=
  (solved_sound_pair hsatisfied).2 left right hsolved

private theorem reconciled_sound_pair
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings) :
    (∀ left right (_ : AtomReconciled bindings left right),
      applyClassSolution valuation (toLeaTTaAtom left) =
        applyClassSolution valuation (toLeaTTaAtom right)) ∧
    (∀ left right (_ : AtomsReconciled bindings left right),
      (toLeaTTaAtoms left).map (applyClassSolution valuation) =
        (toLeaTTaAtoms right).map (applyClassSolution valuation)) := by
  apply reconciled_mutual_induction
  · intro name
    rfl
  · intro left right hclass
    simpa [toLeaTTaAtom, applyClassSolution] using
      hsatisfied.eq_of_mem_eqClass hclass
  · intro left key stored right hassignment hclass htail ih
    have hleftStored : valuation left =
        applyClassSolution valuation (toLeaTTaAtom stored) := by
      simpa [toLeaTTaAtom, applyClassSolution] using
        (hsatisfied.eq_of_mem_eqClass hclass).trans
          (hsatisfied.1 _ _ hassignment)
    simpa [toLeaTTaAtom, applyClassSolution] using
      hleftStored.trans ih
  · intro left stored key right hassignment hclass htail ih
    have hrightStored : valuation right =
        applyClassSolution valuation (toLeaTTaAtom stored) := by
      simpa [toLeaTTaAtom, applyClassSolution] using
        (hsatisfied.eq_of_mem_eqClass hclass).trans
          (hsatisfied.1 _ _ hassignment)
    simpa [toLeaTTaAtom, applyClassSolution] using
      ih.trans hrightStored.symm
  · intro value
    rfl
  · intro left right hitems ih
    simp only [toLeaTTaAtom, applyClassSolution]
    congr 1
  · rfl
  · intro left right lefts rights hhead htail ihHead ihTail
    simp only [toLeaTTaAtoms, List.map_cons, List.cons.injEq]
    exact ⟨ihHead, ihTail⟩

/-- Directional recursive reconciliation is sound in every model of the
binding record. -/
theorem AtomReconciled.sound
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    {left right : Atom}
    (hreconciled : AtomReconciled bindings left right) :
    applyClassSolution valuation (toLeaTTaAtom left) =
      applyClassSolution valuation (toLeaTTaAtom right) :=
  (reconciled_sound_pair hsatisfied).1 left right hreconciled

/-- List companion of `AtomReconciled.sound`. -/
theorem AtomsReconciled.sound
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    {left right : List Atom}
    (hreconciled : AtomsReconciled bindings left right) :
    (toLeaTTaAtoms left).map (applyClassSolution valuation) =
      (toLeaTTaAtoms right).map (applyClassSolution valuation) :=
  (reconciled_sound_pair hsatisfied).2 left right hreconciled

private theorem reconciled_mono_pair
    {before after : Bindings}
    (hsubrecord : BindingSubrecord before after) :
    (∀ left right (_ : AtomReconciled before left right),
      AtomReconciled after left right) ∧
    (∀ left right (_ : AtomsReconciled before left right),
      AtomsReconciled after left right) := by
  apply reconciled_mutual_induction
  · intro name
    exact .symbol name
  · intro left right hclass
    exact .varVar (hsubrecord.mem_eqClass hclass)
  · intro left key stored right hassignment hclass htail ih
    exact .assignedLeft
      (hsubrecord.1 _ hassignment)
      (hsubrecord.mem_eqClass hclass) ih
  · intro left stored key right hassignment hclass htail ih
    exact .assignedRight
      (hsubrecord.1 _ hassignment)
      (hsubrecord.mem_eqClass hclass) ih
  · intro value
    exact .grounded value
  · intro left right hitems ih
    exact .expression ih
  · exact .nil
  · intro left right lefts rights hhead htail ihHead ihTail
    exact .cons ihHead ihTail

/-- Directional reconciliation is monotone under literal binding extension. -/
theorem AtomReconciled.mono
    {before after : Bindings}
    (hsubrecord : BindingSubrecord before after)
    {left right : Atom}
    (hreconciled : AtomReconciled before left right) :
    AtomReconciled after left right :=
  (reconciled_mono_pair hsubrecord).1 left right hreconciled

/-- List companion of `AtomReconciled.mono`. -/
theorem AtomsReconciled.mono
    {before after : Bindings}
    (hsubrecord : BindingSubrecord before after)
    {left right : List Atom}
    (hreconciled : AtomsReconciled before left right) :
    AtomsReconciled after left right :=
  (reconciled_mono_pair hsubrecord).2 left right hreconciled

/-- A source reconciliation certificate remains valid in every literal
extension of its target. -/
theorem ClassAssignmentsReconciledIn.monoTarget
    {firstTarget finalTarget source : Bindings}
    (hrooted : ClassAssignmentsReconciledIn firstTarget source)
    (hsubrecord : BindingSubrecord firstTarget finalTarget) :
    ClassAssignmentsReconciledIn finalTarget source := by
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
      hpivotLeft, hpivotRight⟩ := hrooted hleft hright hclass
  exact ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
    hpivotLeft.mono hsubrecord,
    hpivotRight.mono hsubrecord⟩

mutual

/-- Structural solvedness is reflexive on every atom shape. -/
theorem AtomSolved.refl (bindings : Bindings) (atom : Atom) :
    AtomSolved bindings atom atom := by
  cases atom with
  | symbol name => exact .symbol name
  | var name =>
      exact .varVar
        (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  | grounded value => exact .grounded value
  | expression atoms => exact .expression (AtomsSolved.refl bindings atoms)
termination_by 2 * sizeOf atom

/-- List companion of `AtomSolved.refl`. -/
theorem AtomsSolved.refl (bindings : Bindings) (atoms : List Atom) :
    AtomsSolved bindings atoms atoms := by
  cases atoms with
  | nil => exact .nil
  | cons atom atoms =>
      exact .cons (AtomSolved.refl bindings atom)
        (AtomsSolved.refl bindings atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end

mutual

/-- Directional reconciliation is reflexive on every atom. -/
theorem AtomReconciled.refl (bindings : Bindings) (atom : Atom) :
    AtomReconciled bindings atom atom := by
  cases atom with
  | symbol name => exact .symbol name
  | var name =>
      exact .varVar
        (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  | grounded value => exact .grounded value
  | expression atoms =>
      exact .expression (AtomsReconciled.refl bindings atoms)
termination_by 2 * sizeOf atom

/-- List companion of `AtomReconciled.refl`. -/
theorem AtomsReconciled.refl (bindings : Bindings) (atoms : List Atom) :
    AtomsReconciled bindings atoms atoms := by
  cases atoms with
  | nil => exact .nil
  | cons atom atoms =>
      exact .cons (AtomReconciled.refl bindings atom)
        (AtomsReconciled.refl bindings atoms)
termination_by 2 * sizeOf atoms + 1
decreasing_by all_goals simp_wf <;> omega

end

/-- Pairwise structural coherence is a sufficient, but not necessary, rooted
certificate. -/
theorem structurallyRooted_of_structurallySolved
    {bindings : Bindings}
    (hsolved : ClassAssignmentsStructurallySolved bindings) :
    ClassAssignmentsStructurallyRooted bindings := by
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  exact ⟨leftKey, leftValue, hleft,
    EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
    AtomSolved.refl bindings leftValue,
    hsolved hleft hright hclass⟩

/-- A pointwise structural solution from a replicated pivot exposes a solution
from that pivot to every element of the right-hand list. -/
theorem AtomsSolved.each_of_replicate
    {bindings : Bindings} {pivot : Atom} {values : List Atom}
    (hsolved : AtomsSolved bindings
      (List.replicate values.length pivot) values) :
    ∀ value ∈ values, AtomSolved bindings pivot value := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons, List.replicate_succ] at hsolved
      cases hsolved with
      | cons hhead htail =>
          intro candidate hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact ih htail candidate hmem

/-- Directional list reconciliation from a replicated pivot exposes the pivot
equation for every right-hand element. -/
theorem AtomsReconciled.each_of_replicate
    {bindings : Bindings} {pivot : Atom} {values : List Atom}
    (hreconciled : AtomsReconciled bindings
      (List.replicate values.length pivot) values) :
    ∀ value ∈ values, AtomReconciled bindings pivot value := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons, List.replicate_succ] at hreconciled
      cases hreconciled with
      | cons hhead htail =>
          intro candidate hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact ih htail candidate hmem

/-! ## Representation-independent binding presentation -/

/-- `target` presents every observable constraint of `source`: each raw
assignment equation is structurally solved in `target`, and the full source
equality closure embeds into the target closure.  This deliberately does not
require assignment-list inclusion, because reconciliation may replace a raw
equation by an equivalent solved equation. -/
structure BindingPresentation (target source : Bindings) : Prop where
  assignments : ∀ key value,
    (key, value) ∈ source.assignments →
      AtomSolved target (.var key) value
  classes : ∀ {left right},
    right ∈ source.eqClass left → right ∈ target.eqClass left

theorem BindingPresentation.refl (bindings : Bindings) :
    BindingPresentation bindings bindings where
  assignments _ _ hmem :=
    .assignedLeft hmem
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  classes hclass := hclass

private theorem solved_symm_pair {bindings : Bindings} :
    (∀ left right (_ : AtomSolved bindings left right),
      AtomSolved bindings right left) ∧
    (∀ left right (_ : AtomsSolved bindings left right),
      AtomsSolved bindings right left) := by
  apply solved_mutual_induction
  · intro name
    exact .symbol name
  · intro left right hclass
    exact .varVar (mem_eqClass_symm hclass)
  · intro left key right hassignment hclass
    exact .assignedRight hassignment hclass
  · intro left key right hassignment hclass
    exact .assignedLeft hassignment hclass
  · intro left key right hclass htail ih
    exact .aliasRight hclass ih
  · intro left key right hclass htail ih
    exact .aliasLeft hclass ih
  · intro value
    exact .grounded value
  · intro left right hitems ih
    exact .expression ih
  · exact .nil
  · intro left right lefts rights hhead htail ihHead ihTail
    exact .cons ihHead ihTail

theorem AtomSolved.symm
    {bindings : Bindings} {left right : Atom}
    (hsolved : AtomSolved bindings left right) :
    AtomSolved bindings right left :=
  solved_symm_pair.1 left right hsolved

theorem AtomsSolved.symm
    {bindings : Bindings} {left right : List Atom}
    (hsolved : AtomsSolved bindings left right) :
    AtomsSolved bindings right left :=
  solved_symm_pair.2 left right hsolved

private theorem solved_transport_pair {source : Bindings} :
    (∀ left right (_ : AtomSolved source left right),
      ∀ {target}, BindingPresentation target source →
        AtomSolved target left right) ∧
    (∀ left right (_ : AtomsSolved source left right),
      ∀ {target}, BindingPresentation target source →
        AtomsSolved target left right) := by
  apply solved_mutual_induction
  · intro name target hpresentation
    exact .symbol name
  · intro left right hclass target hpresentation
    exact .varVar (hpresentation.classes hclass)
  · intro left key right hassignment hclass target hpresentation
    exact .aliasLeft (hpresentation.classes hclass)
      (hpresentation.assignments key right hassignment)
  · intro left key right hassignment hclass target hpresentation
    exact .aliasRight (hpresentation.classes hclass)
      (hpresentation.assignments key left hassignment).symm
  · intro left key right hclass htail ih target hpresentation
    exact .aliasLeft (hpresentation.classes hclass) (ih hpresentation)
  · intro left key right hclass htail ih target hpresentation
    exact .aliasRight (hpresentation.classes hclass) (ih hpresentation)
  · intro value target hpresentation
    exact .grounded value
  · intro left right hitems ih target hpresentation
    exact .expression (ih hpresentation)
  · intro target hpresentation
    exact .nil
  · intro left right lefts rights hhead htail ihHead ihTail
      target hpresentation
    exact .cons (ihHead hpresentation) (ihTail hpresentation)

/-- Structural atom solutions are monotone under semantic presentation, even
when reconciliation changes the concrete assignment list. -/
theorem AtomSolved.transport
    {source target : Bindings} {left right : Atom}
    (hsolved : AtomSolved source left right)
    (hpresentation : BindingPresentation target source) :
    AtomSolved target left right :=
  (solved_transport_pair.1 left right hsolved) hpresentation

/-- List companion of `AtomSolved.transport`. -/
theorem AtomsSolved.transport
    {source target : Bindings} {left right : List Atom}
    (hsolved : AtomsSolved source left right)
    (hpresentation : BindingPresentation target source) :
    AtomsSolved target left right :=
  (solved_transport_pair.2 left right hsolved) hpresentation

/-- Semantic presentation composes without any list-order or representative
side condition. -/
theorem BindingPresentation.trans
    {first second third : Bindings}
    (h₁₂ : BindingPresentation second first)
    (h₂₃ : BindingPresentation third second) :
    BindingPresentation third first where
  assignments key value hmem :=
    (h₁₂.assignments key value hmem).transport h₂₃
  classes hclass := h₂₃.classes (h₁₂.classes hclass)

/-- A rooted source certificate transports monotonically through a later
semantic presentation of its target. -/
theorem ClassAssignmentsStructurallyRootedIn.transportTarget
    {firstTarget finalTarget source : Bindings}
    (hrooted : ClassAssignmentsStructurallyRootedIn firstTarget source)
    (hpresentation : BindingPresentation finalTarget firstTarget) :
    ClassAssignmentsStructurallyRootedIn finalTarget source := by
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
      hpivotLeft, hpivotRight⟩ := hrooted hleft hright hclass
  exact ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
    hpivotLeft.transport hpresentation,
    hpivotRight.transport hpresentation⟩

/-- A rooted record remains rooted when viewed in any target that presents
all of its constraints. -/
theorem ClassAssignmentsStructurallyRooted.transport
    {source target : Bindings}
    (hrooted : ClassAssignmentsStructurallyRooted source)
    (hpresentation : BindingPresentation target source) :
    ClassAssignmentsStructurallyRootedIn target source :=
  ClassAssignmentsStructurallyRootedIn.transportTarget
    hrooted hpresentation

/-- Structural presentation of one neutral human merge constraint. -/
def ConstraintSolved (bindings : Bindings) :
    HumanMatchMergeSpec.Constraint → Prop
  | .value key value => AtomSolved bindings (.var key) value
  | .equality left right => right ∈ bindings.eqClass left

/-- Structural presentation of every constraint in one fold order. -/
def ConstraintsSolved (bindings : Bindings)
    (constraints : List HumanMatchMergeSpec.Constraint) : Prop :=
  ∀ constraint ∈ constraints, ConstraintSolved bindings constraint

theorem ConstraintSolved.transport
    {source target : Bindings}
    (hpresentation : BindingPresentation target source)
    {constraint : HumanMatchMergeSpec.Constraint}
    (hsolved : ConstraintSolved source constraint) :
    ConstraintSolved target constraint := by
  cases constraint with
  | value key value =>
      exact AtomSolved.transport hsolved hpresentation
  | equality left right => exact hpresentation.classes hsolved

theorem ConstraintsSolved.transport
    {source target : Bindings}
    (hpresentation : BindingPresentation target source)
    {constraints : List HumanMatchMergeSpec.Constraint}
    (hsolved : ConstraintsSolved source constraints) :
    ConstraintsSolved target constraints := by
  intro constraint hmem
  exact (hsolved constraint hmem).transport hpresentation

private theorem eqClass_mono_of_equalities_solved
    {source target : Bindings}
    (hsolved : ∀ left right,
      (left, right) ∈ source.equalities →
        right ∈ target.eqClass left) :
    ∀ {start finish},
      finish ∈ source.eqClass start →
        finish ∈ target.eqClass start := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  apply hclass.elim
  intro walk
  induction walk with
  | nil => exact .rfl
  | @cons start next finish hadj tail ih =>
      have hstep :
          (EqualityClosure.edgeGraph target.equalities).Reachable
            start next := by
        rw [EqualityClosure.edgeGraph_adj_iff] at hadj
        rcases hadj.2 with hforward | hreverse
        · rw [← EqualityClosure.mem_eqClass_iff_reachable]
          exact hsolved start next hforward
        · rw [← EqualityClosure.mem_eqClass_iff_reachable]
          exact mem_eqClass_symm (hsolved next start hreverse)
      exact hstep.trans (ih tail.reachable)

/-- Solving a permutation of a record's neutral constraints presents the full
record, including the transitive closure of its raw equality edges. -/
theorem BindingPresentation.of_constraintsSolved
    {source target : Bindings}
    {order : List HumanMatchMergeSpec.Constraint}
    (horder : order.Perm (HumanMatchMergeSpec.constraints source))
    (hsolved : ConstraintsSolved target order) :
    BindingPresentation target source where
  assignments key value hmem := by
    apply hsolved (.value key value)
    exact (List.Perm.mem_iff horder).mpr
      (HumanMatchSolutionTheory.value_mem_constraints_iff.mpr hmem)
  classes := eqClass_mono_of_equalities_solved fun left right hmem => by
    apply hsolved (.equality left right)
    exact (List.Perm.mem_iff horder).mpr
      (HumanMatchSolutionTheory.equality_mem_constraints_iff.mpr hmem)

/-- Adding one equality edge only enlarges equality classes. -/
private theorem eqClass_mono_addEquality
    (bindings : Bindings) (left right : String) :
    ∀ {start finish},
      finish ∈ bindings.eqClass start →
        finish ∈ (bindings.addEquality left right).eqClass start := by
  intro start finish hclass
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
  apply hclass.mono
  intro first second hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · exact ⟨hne, Or.inl (by
      simp [Bindings.addEquality, hforward])⟩
  · exact ⟨hne, Or.inr (by
      simp [Bindings.addEquality, hreverse])⟩

/-- If a start vertex is outside the class created by one new equality edge,
then every path from that start already existed before the edge was added. -/
private noncomputable def edgeGraph_walk_old_of_not_reaches_added
    (bindings : Bindings) (addedLeft addedRight : String)
    {start finish : String}
    (walk : (EqualityClosure.edgeGraph
      (bindings.addEquality addedLeft addedRight).equalities).Walk
        start finish)
    (hnot : ¬(EqualityClosure.edgeGraph
      (bindings.addEquality addedLeft addedRight).equalities).Reachable
        start addedLeft) :
    (EqualityClosure.edgeGraph bindings.equalities).Walk start finish := by
  induction walk with
  | nil => exact .nil
  | @cons start next finish hadj tail ih =>
      have hadjReach := hadj.reachable
      have hnextNot : ¬(EqualityClosure.edgeGraph
          (bindings.addEquality addedLeft addedRight).equalities).Reachable
          next addedLeft := by
        intro hnext
        exact hnot (hadjReach.trans hnext)
      have holdAdj :
          (EqualityClosure.edgeGraph bindings.equalities).Adj start next := by
        rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
        rcases hadj with ⟨hne, hforward | hreverse⟩
        · change (start, next) ∈
              bindings.equalities ++ [(addedLeft, addedRight)] at hforward
          rcases List.mem_append.mp hforward with hold | hnew
          · exact ⟨hne, Or.inl hold⟩
          · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
            rcases hnew with ⟨rfl, rfl⟩
            exact (hnot .rfl).elim
        · change (next, start) ∈
              bindings.equalities ++ [(addedLeft, addedRight)] at hreverse
          rcases List.mem_append.mp hreverse with hold | hnew
          · exact ⟨hne, Or.inr hold⟩
          · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
            rcases hnew with ⟨rfl, rfl⟩
            exact (hnot hadjReach).elim
      exact .cons holdAdj (ih hnextNot)

/-- Outside the newly joined component, adding one equality edge leaves the
old equality closure unchanged. -/
private theorem mem_eqClass_old_of_not_mem_addEquality
    (bindings : Bindings) (addedLeft addedRight : String)
    {start finish : String}
    (hnot : addedLeft ∉
      (bindings.addEquality addedLeft addedRight).eqClass start)
    (hclass : finish ∈
      (bindings.addEquality addedLeft addedRight).eqClass start) :
    finish ∈ bindings.eqClass start := by
  rw [EqualityClosure.mem_eqClass_iff_reachable] at hnot hclass ⊢
  exact hclass.elim fun walk =>
    (edgeGraph_walk_old_of_not_reaches_added
      bindings addedLeft addedRight walk hnot).reachable

/-- The old record is structurally presented after adding an equality edge. -/
theorem BindingPresentation.addEquality
    (bindings : Bindings) (left right : String) :
    BindingPresentation (bindings.addEquality left right) bindings where
  assignments key value hmem :=
    .assignedLeft (by simpa [Bindings.addEquality] using hmem)
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  classes hclass := eqClass_mono_addEquality bindings left right hclass

/-! ## Boundary canaries -/

private def recursiveReconciliationProbe : Bindings :=
  (Bindings.empty.assign "y"
    (.expression [.symbol "g", .var "z"])).assign
      "z" (.symbol "a")

/-- Positive: directional reconciliation recursively reads a stored compound
value and then a second stored leaf. -/
theorem recursiveReconciliationProbe_solves :
    AtomReconciled recursiveReconciliationProbe
      (.var "y")
      (.expression [.symbol "g", .symbol "a"]) := by
  apply AtomReconciled.assignedLeft
      (key := "y")
      (stored := .expression [.symbol "g", .var "z"])
  · simp [recursiveReconciliationProbe, Bindings.assign,
      Bindings.isBound, Bindings.lookup, Bindings.empty]
  · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
  · apply AtomReconciled.expression
    apply AtomsReconciled.cons (.symbol "g")
    apply AtomsReconciled.cons
    · apply AtomReconciled.assignedLeft
        (key := "z") (stored := .symbol "a")
      · simp [recursiveReconciliationProbe, Bindings.assign,
          Bindings.isBound, Bindings.lookup, Bindings.empty]
      · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
      · exact .symbol "a"
    · exact .nil

/-- Negative: recursive dereferencing never invents equality between distinct
symbol heads. -/
theorem symbol_mismatch_not_reconciled
    {bindings : Bindings} {left right : String}
    (hne : left ≠ right) :
    ¬AtomReconciled bindings (.symbol left) (.symbol right) := by
  intro hreconciled
  cases hreconciled with
  | symbol => exact hne rfl

private def structuralSolvedProbe : Bindings :=
  Bindings.empty.assign "y" (.symbol "a")

/-- Positive: a stored variable solution is visible under arbitrarily nested
constructor structure. -/
theorem structuralSolvedProbe_nested :
    AtomSolved structuralSolvedProbe
      (.expression [.symbol "f", .var "y"])
      (.expression [.symbol "f", .symbol "a"]) := by
  apply AtomSolved.expression
  apply AtomsSolved.cons (.symbol "f")
  apply AtomsSolved.cons
  · apply AtomSolved.assignedLeft (key := "y")
    · simp [structuralSolvedProbe, Bindings.assign,
        Bindings.isBound, Bindings.lookup, Bindings.empty]
    · rw [EqualityClosure.mem_eqClass_iff_reachable]
  · exact .nil

/-- Negative: without the reconciliating assignment, the same nested equation
has no structural certificate. -/
theorem empty_not_structuralSolved_nested :
    ¬AtomSolved Bindings.empty
      (.expression [.symbol "f", .var "y"])
      (.expression [.symbol "f", .symbol "a"]) := by
  intro hsolved
  have heq := hsolved.sound
    (hesat_empty (fun name => Metta.Atom.var name))
  simp [toLeaTTaAtom, applyClassSolution] at heq

/-- Negative presentation canary: an empty target cannot present a source
assignment merely by forgetting its equation. -/
theorem empty_not_presents_structuralSolvedProbe :
    ¬BindingPresentation Bindings.empty structuralSolvedProbe := by
  intro hpresentation
  have hmem : ("y", .symbol "a") ∈
      structuralSolvedProbe.assignments := by
    simp [structuralSolvedProbe, Bindings.assign,
      Bindings.isBound, Bindings.lookup, Bindings.empty]
  have hsolved := hpresentation.assignments "y" (.symbol "a") hmem
  have heq := hsolved.sound
    (hesat_empty (fun name => Metta.Atom.var name))
  simp [toLeaTTaAtom, applyClassSolution] at heq

private theorem lookup_mem_of_eq_some {key : String} {value : Atom} :
    ∀ {assignments : List (String × Atom)},
      List.lookup key assignments = some value →
      (key, value) ∈ assignments
  | [], hlookup => by simp at hlookup
  | (storedKey, storedValue) :: assignments, hlookup => by
      by_cases hkey : key = storedKey
      · subst storedKey
        simp at hlookup
        subst storedValue
        simp
      · have hbeq : (key == storedKey) = false := by simp [hkey]
        simp only [List.lookup_cons, hbeq] at hlookup
        exact List.mem_cons_of_mem _ (lookup_mem_of_eq_some hlookup)

private theorem lookup_eq_some_of_mem_nodup
    {assignments : List (String × Atom)}
    (hnodup : (assignments.map Prod.fst).Nodup)
    {key : String} {value : Atom}
    (hmem : (key, value) ∈ assignments) :
    List.lookup key assignments = some value := by
  induction assignments with
  | nil => cases hmem
  | cons binding assignments ih =>
      rcases binding with ⟨storedKey, storedValue⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      have htailNodup : (assignments.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hnodup).2
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        simp
      · have hstoredNotMem : storedKey ∉ assignments.map Prod.fst := by
          simpa using (List.nodup_cons.mp hnodup).1
        have hne : key ≠ storedKey := by
          intro heq
          apply hstoredNotMem
          have hkeyMem : key ∈ assignments.map Prod.fst :=
            List.mem_map.mpr ⟨(key, value), htail, rfl⟩
          simpa [heq] using hkeyMem
        have hbeq : (key == storedKey) = false := by simp [hne]
        simp only [List.lookup_cons, hbeq]
        exact ih htailNodup htail

private theorem key_not_mem_of_lookup_none
    {assignments : List (String × Atom)} {key : String}
    (hlookup : List.lookup key assignments = none) :
    key ∉ assignments.map Prod.fst := by
  intro hmem
  induction assignments with
  | nil => simp at hmem
  | cons binding assignments ih =>
      rcases binding with ⟨storedKey, storedValue⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      by_cases hkey : key = storedKey
      · subst storedKey
        simp at hlookup
      · have hbeq : (key == storedKey) = false := by simp [hkey]
        simp only [List.lookup_cons, hbeq] at hlookup
        rcases hmem with hhead | htail
        · exact hkey hhead
        · exact ih hlookup htail

private theorem isBound_false_of_classValues_nil
    {bindings : Bindings} {key : String}
    (hvalues : bindings.classValues key = []) :
    bindings.isBound key = false := by
  by_contra hnotFalse
  have hbound : bindings.isBound key = true := by
    simpa using hnotFalse
  rw [Bindings.isBound, Option.isSome_iff_exists] at hbound
  rcases hbound with ⟨value, hlookup⟩
  have hself : key ∈ bindings.eqClassOrdered key :=
    EqualityClosure.mem_eqClassOrdered_iff.mpr
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  have hvalue : value ∈ bindings.classValues key := by
    unfold Bindings.classValues
    exact List.mem_filterMap.mpr ⟨key, hself, hlookup⟩
  simp [hvalues] at hvalue

private theorem assignmentsNodup_assign
    {bindings : Bindings} {key : String} {value : Atom}
    (hnodup : AssignmentsNodup bindings) :
    AssignmentsNodup (bindings.assign key value) := by
  unfold AssignmentsNodup at hnodup ⊢
  by_cases hbound : bindings.isBound key
  · have hkeys :
        ((bindings.assignments.map fun assignment =>
            if (assignment.1 == key) = true then
              (assignment.1, value)
            else (assignment.1, assignment.2)).map Prod.fst) =
          bindings.assignments.map Prod.fst := by
      rw [List.map_map]
      apply List.map_congr_left
      intro assignment hmem
      rcases assignment with ⟨storedKey, storedValue⟩
      by_cases hstored : storedKey = key <;> simp [hstored]
    simp only [Bindings.assign, if_pos hbound]
    rw [hkeys]
    exact hnodup
  · have hlookup : bindings.lookup key = none := by
      unfold Bindings.isBound at hbound
      cases h : bindings.lookup key <;> simp [h] at hbound ⊢
    have hnotmem := key_not_mem_of_lookup_none hlookup
    simp only [Bindings.assign, if_neg hbound, List.map_append,
      List.map_singleton]
    simpa only [List.concat_eq_append] using
      List.Nodup.concat hnotmem hnodup

/-- Successful human matching preserves the binding representation's unique
assignment-key invariant through every recursive reconciliation branch. -/
theorem humanMatch_assignmentsNodup
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out) :
    AssignmentsNodup out := by
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun _ _ out _ => AssignmentsNodup out)
    (motive_2 := fun _ _ seed out _ =>
      AssignmentsNodup seed → AssignmentsNodup out)
    (motive_3 := fun seed _ _ out _ =>
      AssignmentsNodup seed → AssignmentsNodup out)
    (motive_4 := fun seed _ _ out _ =>
      AssignmentsNodup seed → AssignmentsNodup out)
    (motive_5 := fun seed _ out _ =>
      AssignmentsNodup seed → AssignmentsNodup out)
    (motive_6 := fun left _ out _ =>
      AssignmentsNodup left → AssignmentsNodup out)
    (t := hmatch)
  next => intros; simp [AssignmentsNodup, Bindings.empty]
  next => intros; simp [AssignmentsNodup, Bindings.empty,
    Bindings.addEquality]
  next =>
      intro varName value hnonvar hadmissible
      exact assignmentsNodup_assign (by
        simp [AssignmentsNodup, Bindings.empty])
  next =>
      intro value varName hnonvar hadmissible
      exact assignmentsNodup_assign (by
        simp [AssignmentsNodup, Bindings.empty])
  next =>
      intro left right out hitems hadmissible ih
      exact ih (by simp [AssignmentsNodup, Bindings.empty])
  next =>
      intro grounded right out hright hcustom hmatch hadmissible
      rcases hmatch with ⟨hrightEq, hout⟩
      subst right
      subst out
      simp [AssignmentsNodup, Bindings.empty]
  next =>
      intro left grounded out hleft hleftNoCustom hcustom hmatch hadmissible
      rcases hmatch with ⟨hleftEq, hout⟩
      subst left
      subst out
      simp [AssignmentsNodup, Bindings.empty]
  next => intros; simp [AssignmentsNodup, Bindings.empty]
  next => intro seed; exact fun hseed => hseed
  next =>
      intro left right lefts rights seed matched next out
        hhead hmerge htail ihHead ihMerge ihTail hseed
      exact ihTail (ihMerge hseed)
  next =>
      intro seed varName value hvalues hseed
      exact assignmentsNodup_assign hseed
  next => intros; assumption
  next =>
      intro seed varName value first rest matched out hvalues hagree hne
        hhead hmerge ihHead ihMerge hseed
      exact ihMerge hseed
  next =>
      intro seed varName value first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge hseed
      exact ihMerge hseed
  next => intros; assumption
  next =>
      intro seed left right first rest matched out hvalues hnotAgree
        hlist hmerge ihList ihMerge hseed
      exact ihMerge hseed
  next => intro seed; exact fun hseed => hseed
  next =>
      intro seed next out varName value rest hadd htail ihAdd ihTail hseed
      exact ihTail (ihAdd hseed)
  next =>
      intro seed next out left right rest hadd htail ihAdd ihTail hseed
      exact ihTail (ihAdd hseed)
  next =>
      intro left right out order horder hfold ihFold hleft
      exact ihFold hleft

/-- Under unique assignment keys, every stored assignment is one of the
values visible from every variable in its equality class. -/
theorem assignment_value_mem_classValues
    {bindings : Bindings}
    (hnodup : AssignmentsNodup bindings)
    {name key : String} {value : Atom}
    (hassignment : (key, value) ∈ bindings.assignments)
    (hclass : key ∈ bindings.eqClass name) :
    value ∈ bindings.classValues name := by
  unfold Bindings.classValues
  apply List.mem_filterMap.mpr
  refine ⟨key, EqualityClosure.mem_eqClassOrdered_iff.mpr hclass, ?_⟩
  exact lookup_eq_some_of_mem_nodup hnodup hassignment

/-- Every visible class value comes from a concrete stored assignment whose
key lies in that class. -/
theorem exists_assignment_of_mem_classValues
    {bindings : Bindings} {name : String} {value : Atom}
    (hvalue : value ∈ bindings.classValues name) :
    ∃ key,
      (key, value) ∈ bindings.assignments ∧
        key ∈ bindings.eqClass name := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with
    ⟨key, hkeyOrdered, hlookup⟩
  exact ⟨key, lookup_mem_of_eq_some hlookup,
    EqualityClosure.mem_eqClassOrdered_iff.mp hkeyOrdered⟩

/-- In a class declared syntactically coherent, any two visible values agree;
the statement is independent of which one happens to be the list head. -/
theorem valuesAgree_eq_of_mem
    {values : List Atom}
    (hagree : HumanMatchMergeSpec.ValuesAgree values)
    {left right : Atom}
    (hleft : left ∈ values) (hright : right ∈ values) :
    left = right := by
  cases values with
  | nil => simp at hleft
  | cons first rest =>
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · rfl
        · exact (hagree right hright).symm
      · rcases hright with rfl | hright
        · exact hagree left hleft
        · exact (hagree left hleft).trans
            (hagree right hright).symm

/-- Adding the first value in an equality class preserves structural class
coherence.  The empty `classValues` premise rules out a hidden old assignment
in that class; unique keys ensure the lookup view has not hidden one. -/
theorem structurallySolved_assign_of_classValues_nil
    {bindings : Bindings} {key : String} {value : Atom}
    (hsolved : ClassAssignmentsStructurallySolved bindings)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : bindings.classValues key = []) :
    ClassAssignmentsStructurallySolved (bindings.assign key value) := by
  have hbound := isBound_false_of_classValues_nil hvalues
  have hpresentation :
      BindingPresentation (bindings.assign key value) bindings := by
    constructor
    · intro oldKey oldValue hmem
      apply AtomSolved.assignedLeft (key := oldKey)
      · simp [Bindings.assign, hbound, hmem]
      · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
    · intro left right hclass
      simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftCases :
      (leftKey, leftValue) ∈ bindings.assignments ∨
        (leftKey = key ∧ leftValue = value) := by
    simpa [Bindings.assign, hbound] using hleft
  have hrightCases :
      (rightKey, rightValue) ∈ bindings.assignments ∨
        (rightKey = key ∧ rightValue = value) := by
    simpa [Bindings.assign, hbound] using hright
  have hclassOld : rightKey ∈ bindings.eqClass leftKey := by
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  rcases hleftCases with hleftOld | hleftNew
  · rcases hrightCases with hrightOld | hrightNew
    · exact (hsolved hleftOld hrightOld hclassOld).transport
        hpresentation
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      have hleftClass : leftKey ∈ bindings.eqClass key := by
        rw [hrightKey] at hclassOld
        exact mem_eqClass_symm hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hleftOld hleftClass
      rw [hvalues] at hvisible
      simp at hvisible
  · rcases hleftNew with ⟨hleftKey, hleftValue⟩
    rcases hrightCases with hrightOld | hrightNew
    · have hrightClass : rightKey ∈ bindings.eqClass key := by
        simpa [hleftKey] using hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hrightOld hrightClass
      rw [hvalues] at hvisible
      simp at hvisible
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      simpa [hleftValue, hrightValue] using
        AtomSolved.refl (bindings.assign key value) value

/-- Joining two equality classes preserves structural coherence whenever all
values visible in the joined class agree.  Classes outside that component are
unchanged by the new edge. -/
theorem structurallySolved_addEquality_of_valuesAgree
    {bindings : Bindings} {left right : String}
    (hsolved : ClassAssignmentsStructurallySolved bindings)
    (hnodup : AssignmentsNodup bindings)
    (hagree : HumanMatchMergeSpec.ValuesAgree
      ((bindings.addEquality left right).classValues left)) :
    ClassAssignmentsStructurallySolved
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  have hpresentation : BindingPresentation candidate bindings := by
    simpa [candidate] using BindingPresentation.addEquality bindings left right
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hvalueEq := valuesAgree_eq_of_mem
      hagree hleftVisible hrightVisible
    subst rightValue
    exact AtomSolved.refl candidate leftValue
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    exact (hsolved hleftOld hrightOld hclassOld).transport hpresentation

/-- Adding the first value in a class preserves a rooted certificate viewed in
any later target. -/
theorem structurallyRootedIn_assign_of_classValues_nil
    {target bindings : Bindings} {key : String} {value : Atom}
    (hrooted : ClassAssignmentsStructurallyRootedIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : bindings.classValues key = []) :
    ClassAssignmentsStructurallyRootedIn target
      (bindings.assign key value) := by
  have hbound := isBound_false_of_classValues_nil hvalues
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftCases :
      (leftKey, leftValue) ∈ bindings.assignments ∨
        (leftKey = key ∧ leftValue = value) := by
    simpa [Bindings.assign, hbound] using hleft
  have hrightCases :
      (rightKey, rightValue) ∈ bindings.assignments ∨
        (rightKey = key ∧ rightValue = value) := by
    simpa [Bindings.assign, hbound] using hright
  have hclassOld : rightKey ∈ bindings.eqClass leftKey := by
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  rcases hleftCases with hleftOld | hleftNew
  · rcases hrightCases with hrightOld | hrightNew
    · obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
          hpivotLeft, hpivotRight⟩ :=
        hrooted hleftOld hrightOld hclassOld
      exact ⟨pivotKey, pivotValue,
        by
          simpa [Bindings.assign, hbound] using
            List.mem_append_left [(key, value)] hpivotMem,
        by simpa [Bindings.eqClass, Bindings.assign, hbound] using hpivotClass,
        hpivotLeft, hpivotRight⟩
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      have hleftClass : leftKey ∈ bindings.eqClass key := by
        rw [hrightKey] at hclassOld
        exact mem_eqClass_symm hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hleftOld hleftClass
      rw [hvalues] at hvisible
      simp at hvisible
  · rcases hleftNew with ⟨hleftKey, hleftValue⟩
    rcases hrightCases with hrightOld | hrightNew
    · have hrightClass : rightKey ∈ bindings.eqClass key := by
        simpa [hleftKey] using hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hrightOld hrightClass
      rw [hvalues] at hvisible
      simp at hvisible
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      refine ⟨leftKey, leftValue, hleft, ?_, ?_, ?_⟩
      · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
      · exact AtomSolved.refl target leftValue
      · simpa [hleftValue, hrightValue] using
          AtomSolved.refl target value

/-- Directional reconciliation is preserved when a class receives its first
stored value. -/
theorem reconciledIn_assign_of_classValues_nil
    {target bindings : Bindings} {key : String} {value : Atom}
    (hreconciled : ClassAssignmentsReconciledIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : bindings.classValues key = []) :
    ClassAssignmentsReconciledIn target
      (bindings.assign key value) := by
  have hbound := isBound_false_of_classValues_nil hvalues
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftCases :
      (leftKey, leftValue) ∈ bindings.assignments ∨
        (leftKey = key ∧ leftValue = value) := by
    simpa [Bindings.assign, hbound] using hleft
  have hrightCases :
      (rightKey, rightValue) ∈ bindings.assignments ∨
        (rightKey = key ∧ rightValue = value) := by
    simpa [Bindings.assign, hbound] using hright
  have hclassOld : rightKey ∈ bindings.eqClass leftKey := by
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  rcases hleftCases with hleftOld | hleftNew
  · rcases hrightCases with hrightOld | hrightNew
    · obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
          hpivotLeft, hpivotRight⟩ :=
        hreconciled hleftOld hrightOld hclassOld
      exact ⟨pivotKey, pivotValue,
        by
          simpa [Bindings.assign, hbound] using
            List.mem_append_left [(key, value)] hpivotMem,
        by simpa [Bindings.eqClass, Bindings.assign, hbound] using hpivotClass,
        hpivotLeft, hpivotRight⟩
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      have hleftClass : leftKey ∈ bindings.eqClass key := by
        rw [hrightKey] at hclassOld
        exact mem_eqClass_symm hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hleftOld hleftClass
      rw [hvalues] at hvisible
      simp at hvisible
  · rcases hleftNew with ⟨hleftKey, hleftValue⟩
    rcases hrightCases with hrightOld | hrightNew
    · have hrightClass : rightKey ∈ bindings.eqClass key := by
        simpa [hleftKey] using hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hrightOld hrightClass
      rw [hvalues] at hvisible
      simp at hvisible
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      refine ⟨leftKey, leftValue, hleft, ?_, ?_, ?_⟩
      · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
      · exact AtomReconciled.refl target leftValue
      · simpa [hleftValue, hrightValue] using
          AtomReconciled.refl target value

/-- Joining classes whose visible values are literally equal preserves a
rooted certificate in any target. -/
theorem structurallyRootedIn_addEquality_of_valuesAgree
    {target bindings : Bindings} {left right : String}
    (hrooted : ClassAssignmentsStructurallyRootedIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hagree : HumanMatchMergeSpec.ValuesAgree
      ((bindings.addEquality left right).classValues left)) :
    ClassAssignmentsStructurallyRootedIn target
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hvalueEq := valuesAgree_eq_of_mem
      hagree hleftVisible hrightVisible
    subst rightValue
    exact ⟨leftKey, leftValue, hleft,
      EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
      AtomSolved.refl target leftValue,
      AtomSolved.refl target leftValue⟩
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
        hpivotLeft, hpivotRight⟩ :=
      hrooted hleftOld hrightOld hclassOld
    exact ⟨pivotKey, pivotValue,
      by simpa [candidate, Bindings.addEquality] using hpivotMem,
      by simpa [candidate] using
        eqClass_mono_addEquality bindings left right hpivotClass,
      hpivotLeft, hpivotRight⟩

/-- Joining classes with literally equal visible values preserves directional
reconciliation in any target. -/
theorem reconciledIn_addEquality_of_valuesAgree
    {target bindings : Bindings} {left right : String}
    (hreconciled : ClassAssignmentsReconciledIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hagree : HumanMatchMergeSpec.ValuesAgree
      ((bindings.addEquality left right).classValues left)) :
    ClassAssignmentsReconciledIn target
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hvalueEq := valuesAgree_eq_of_mem
      hagree hleftVisible hrightVisible
    subst rightValue
    exact ⟨leftKey, leftValue, hleft,
      EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
      AtomReconciled.refl target leftValue,
      AtomReconciled.refl target leftValue⟩
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotClass,
        hpivotLeft, hpivotRight⟩ :=
      hreconciled hleftOld hrightOld hclassOld
    exact ⟨pivotKey, pivotValue,
      by simpa [candidate, Bindings.addEquality] using hpivotMem,
      by simpa [candidate] using
        eqClass_mono_addEquality bindings left right hpivotClass,
      hpivotLeft, hpivotRight⟩

/-- The reconciliation branch joins two classes and then supplies a structural
solution from one visible pivot to every value in the joined class.  That
star-shaped witness is exactly enough to root the temporary equality
candidate, without any generic transitivity principle. -/
theorem structurallyRootedIn_addEquality_of_pivotSolved
    {target bindings : Bindings} {left right : String}
    {first : Atom} {rest : List Atom}
    (hrooted : ClassAssignmentsStructurallyRootedIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : (first :: rest).Perm
      ((bindings.addEquality left right).classValues left))
    (hpivotSolved : ∀ value ∈ first :: rest,
      AtomSolved target first value) :
    ClassAssignmentsStructurallyRootedIn target
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  have hfirstVisible : first ∈ candidate.classValues left := by
    exact (List.Perm.mem_iff hvalues).mp (by simp)
  obtain ⟨pivotKey, hpivotMem, hpivotJoined⟩ :=
    exists_assignment_of_mem_classValues hfirstVisible
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hleftList : leftValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hleftVisible
    have hrightList : rightValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hrightVisible
    have hpivotClass : pivotKey ∈ candidate.eqClass leftKey := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hpivotJoined hjoined ⊢
      exact hjoined.symm.trans hpivotJoined
    exact ⟨pivotKey, first, hpivotMem, hpivotClass,
      hpivotSolved leftValue hleftList,
      hpivotSolved rightValue hrightList⟩
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    obtain ⟨oldPivotKey, oldPivotValue, holdPivotMem, holdPivotClass,
        holdPivotLeft, holdPivotRight⟩ :=
      hrooted hleftOld hrightOld hclassOld
    exact ⟨oldPivotKey, oldPivotValue,
      by simpa [candidate, Bindings.addEquality] using holdPivotMem,
      by simpa [candidate] using
        eqClass_mono_addEquality bindings left right holdPivotClass,
      holdPivotLeft, holdPivotRight⟩

/-- Directional counterpart of the equality-reconciliation pivot lemma. -/
theorem reconciledIn_addEquality_of_pivotReconciled
    {target bindings : Bindings} {left right : String}
    {first : Atom} {rest : List Atom}
    (hreconciled : ClassAssignmentsReconciledIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : (first :: rest).Perm
      ((bindings.addEquality left right).classValues left))
    (hpivotReconciled : ∀ value ∈ first :: rest,
      AtomReconciled target first value) :
    ClassAssignmentsReconciledIn target
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  have hfirstVisible : first ∈ candidate.classValues left := by
    exact (List.Perm.mem_iff hvalues).mp (by simp)
  obtain ⟨pivotKey, hpivotMem, hpivotJoined⟩ :=
    exists_assignment_of_mem_classValues hfirstVisible
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hleftList : leftValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hleftVisible
    have hrightList : rightValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hrightVisible
    have hpivotClass : pivotKey ∈ candidate.eqClass leftKey := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hpivotJoined hjoined ⊢
      exact hjoined.symm.trans hpivotJoined
    exact ⟨pivotKey, first, hpivotMem, hpivotClass,
      hpivotReconciled leftValue hleftList,
      hpivotReconciled rightValue hrightList⟩
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    obtain ⟨oldPivotKey, oldPivotValue, holdPivotMem, holdPivotClass,
        holdPivotLeft, holdPivotRight⟩ :=
      hreconciled hleftOld hrightOld hclassOld
    exact ⟨oldPivotKey, oldPivotValue,
      by simpa [candidate, Bindings.addEquality] using holdPivotMem,
      by simpa [candidate] using
        eqClass_mono_addEquality bindings left right holdPivotClass,
      holdPivotLeft, holdPivotRight⟩

/-- A visible class value reifies as a stored assignment in the stable
representative's class. -/
theorem exists_classAssignment_of_mem_classValues
    {bindings : Bindings} {name : String} {value : Atom}
    (hvalue : value ∈ bindings.classValues name) :
    ∃ assignment :
        ClassAssignment bindings (bindings.eqRepresentative name),
      assignment.1.2 = value := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with
    ⟨key, hkeyOrdered, hlookup⟩
  have hkeyClass : key ∈ bindings.eqClass name :=
    EqualityClosure.mem_eqClassOrdered_iff.mp hkeyOrdered
  have hrepToName : name ∈
      bindings.eqClass (bindings.eqRepresentative name) :=
    mem_eqClass_symm (eqRepresentative_mem_eqClass bindings name)
  have hkeyRep : key ∈
      bindings.eqClass (bindings.eqRepresentative name) := by
    rw [EqualityClosure.mem_eqClass_iff_reachable] at hrepToName hkeyClass ⊢
    exact hrepToName.trans hkeyClass
  exact ⟨⟨(key, value), lookup_mem_of_eq_some hlookup, hkeyRep⟩, rfl⟩

private theorem reconciled_canonical_pair
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (hsmaller : ∀ target : DependencyNode bindings,
      DependencyOrder bindings target source →
      ∀ assignment : ClassAssignment bindings target.1,
        canonicalNodeValue bindings hloopFree hnonvariable target =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2)) :
    (∀ left right (_ : AtomReconciled bindings left right),
      AtomDependenciesBelow bindings source left →
      AtomDependenciesBelow bindings source right →
      applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom left) =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom right)) ∧
    (∀ left right (_ : AtomsReconciled bindings left right),
      (∀ atom, atom ∈ left →
        AtomDependenciesBelow bindings source atom) →
      (∀ atom, atom ∈ right →
        AtomDependenciesBelow bindings source atom) →
      (toLeaTTaAtoms left).map
          (applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)) =
        (toLeaTTaAtoms right).map
          (applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable))) := by
  apply reconciled_mutual_induction
  · intro name hleftBelow hrightBelow
    rfl
  · intro left right hclass hleftBelow hrightBelow
    obtain ⟨hleftSupport, _hleftLt⟩ :=
      hleftBelow left (.var left)
    simpa [toLeaTTaAtom, applyClassSolution] using
      canonicalValuation_eq_of_mem_eqClass
        hloopFree hnonvariable hleftSupport hclass
  · intro left key stored right hassignment hclass htail ih
      hleftBelow hrightBelow
    obtain ⟨hleftSupport, hleftLt⟩ :=
      hleftBelow left (.var left)
    let target : DependencyNode bindings :=
      representativeNode ⟨left, hleftSupport⟩
    have hleftTarget : left ∈ bindings.eqClass target.1 := by
      change left ∈ bindings.eqClass
        (bindings.eqRepresentative left)
      exact mem_eqClass_symm
        (eqRepresentative_mem_eqClass bindings left)
    have hkeyTarget : key ∈ bindings.eqClass target.1 := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hleftTarget hclass ⊢
      exact hleftTarget.trans hclass
    let assignment : ClassAssignment bindings target.1 :=
      ⟨(key, stored), hassignment, hkeyTarget⟩
    have hleftStored :
        canonicalValuation bindings hloopFree hnonvariable left =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom stored) := by
      have htargetStored := hsmaller target hleftLt assignment
      simpa [canonicalValuation, hleftSupport, target] using
        htargetStored
    have htailEq := ih
      (ClassAssignment.value_dependenciesBelow
        hnonvariable hleftLt assignment)
      hrightBelow
    simpa [toLeaTTaAtom, applyClassSolution] using
      hleftStored.trans htailEq
  · intro left stored key right hassignment hclass htail ih
      hleftBelow hrightBelow
    obtain ⟨hrightSupport, hrightLt⟩ :=
      hrightBelow right (.var right)
    let target : DependencyNode bindings :=
      representativeNode ⟨right, hrightSupport⟩
    have hrightTarget : right ∈ bindings.eqClass target.1 := by
      change right ∈ bindings.eqClass
        (bindings.eqRepresentative right)
      exact mem_eqClass_symm
        (eqRepresentative_mem_eqClass bindings right)
    have hkeyTarget : key ∈ bindings.eqClass target.1 := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hrightTarget hclass ⊢
      exact hrightTarget.trans hclass
    let assignment : ClassAssignment bindings target.1 :=
      ⟨(key, stored), hassignment, hkeyTarget⟩
    have hrightStored :
        canonicalValuation bindings hloopFree hnonvariable right =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom stored) := by
      have htargetStored := hsmaller target hrightLt assignment
      simpa [canonicalValuation, hrightSupport, target] using
        htargetStored
    have htailEq := ih hleftBelow
      (ClassAssignment.value_dependenciesBelow
        hnonvariable hrightLt assignment)
    simpa [toLeaTTaAtom, applyClassSolution] using
      htailEq.trans hrightStored.symm
  · intro value hleftBelow hrightBelow
    rfl
  · intro left right hitems ih hleftBelow hrightBelow
    simp only [toLeaTTaAtom, applyClassSolution]
    congr 1
    exact ih
      (fun atom hatom name hoccurs =>
        hleftBelow name (.expression hatom hoccurs))
      (fun atom hatom name hoccurs =>
        hrightBelow name (.expression hatom hoccurs))
  · intro hleftBelow hrightBelow
    rfl
  · intro left right lefts rights hhead htail ihHead ihTail
      hleftBelow hrightBelow
    simp only [toLeaTTaAtoms, List.map_cons, List.cons.injEq]
    constructor
    · exact ihHead
        (hleftBelow left (by simp))
        (hrightBelow right (by simp))
    · exact ihTail
        (fun atom hatom => hleftBelow atom (by simp [hatom]))
        (fun atom hatom => hrightBelow atom (by simp [hatom]))

/-- Directional recursive reconciliation evaluates equally in the canonical
valuation whenever every variable it dereferences belongs to a strictly
smaller dependency class. -/
theorem AtomReconciled.canonical_eq_of_below
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (hsmaller : ∀ target : DependencyNode bindings,
      DependencyOrder bindings target source →
      ∀ assignment : ClassAssignment bindings target.1,
        canonicalNodeValue bindings hloopFree hnonvariable target =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right : Atom}
    (hreconciled : AtomReconciled bindings left right)
    (hleftBelow : AtomDependenciesBelow bindings source left)
    (hrightBelow : AtomDependenciesBelow bindings source right) :
    applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom left) =
      applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom right) :=
  (reconciled_canonical_pair hloopFree hnonvariable hsmaller).1
    left right hreconciled hleftBelow hrightBelow

/-- Directional class reconciliation discharges the canonical model's class
coherence obligation.  All recursive assignment reads are justified by the
strict dependency order, while the common pivot avoids any appeal to generic
transitivity. -/
theorem canonicalClassCoherent_of_reconciled
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hreconciled : ClassAssignmentsReconciled bindings) :
    CanonicalClassCoherent bindings hloopFree hnonvariable := by
  unfold CanonicalClassCoherent
  intro source
  let NodeCoherent : DependencyNode bindings → Prop := fun node =>
    ∀ assignment : ClassAssignment bindings node.1,
      canonicalNodeValue bindings hloopFree hnonvariable node =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom assignment.1.2)
  change NodeCoherent source
  apply (dependencyOrder_wellFounded hloopFree).induction source
  intro source hsmaller assignment
  cases hchosen : chosenClassAssignment bindings source.1 with
  | none =>
      have hnonempty : Nonempty (ClassAssignment bindings source.1) :=
        ⟨assignment⟩
      simp [chosenClassAssignment, hnonempty] at hchosen
  | some chosen =>
      have hchosenToAssignment : assignment.1.1 ∈
          bindings.eqClass chosen.1.1 := by
        have hchosenClass := chosen.2.2
        have hassignmentClass := assignment.2.2
        rw [EqualityClosure.mem_eqClass_iff_reachable]
          at hchosenClass hassignmentClass ⊢
        exact hchosenClass.symm.trans hassignmentClass
      obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotToChosen,
          hpivotChosen, hpivotAssignment⟩ :=
        hreconciled chosen.2.1 assignment.2.1 hchosenToAssignment
      have hpivotClass : pivotKey ∈ bindings.eqClass source.1 := by
        have hchosenClass := chosen.2.2
        rw [EqualityClosure.mem_eqClass_iff_reachable]
          at hchosenClass hpivotToChosen ⊢
        exact hchosenClass.trans hpivotToChosen
      let pivot : ClassAssignment bindings source.1 :=
        ⟨(pivotKey, pivotValue), hpivotMem, hpivotClass⟩
      have hpivotBelow :=
        ClassAssignment.value_dependenciesBelow_source
          hnonvariable pivot
      have hchosenBelow :=
        ClassAssignment.value_dependenciesBelow_source
          hnonvariable chosen
      have hassignmentBelow :=
        ClassAssignment.value_dependenciesBelow_source
          hnonvariable assignment
      have hpivotChosenEq :
          applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom pivotValue) =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom chosen.1.2) :=
        AtomReconciled.canonical_eq_of_below
          hloopFree hnonvariable hsmaller hpivotChosen
          hpivotBelow hchosenBelow
      have hpivotAssignmentEq :
          applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom pivotValue) =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom assignment.1.2) :=
        AtomReconciled.canonical_eq_of_below
          hloopFree hnonvariable hsmaller hpivotAssignment
          hpivotBelow hassignmentBelow
      calc
        canonicalNodeValue bindings hloopFree hnonvariable source =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom chosen.1.2) :=
          canonicalNodeValue_eq_applyClassSolution_of_chosen
            hloopFree hnonvariable chosen hchosen
        _ = applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom assignment.1.2) :=
          hpivotChosenEq.symm.trans hpivotAssignmentEq

/-- A loop-free, non-variable record with derivational reconciliation has a
concrete canonical model. -/
theorem has_model_of_reconciled
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hreconciled : ClassAssignmentsReconciled bindings) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings := by
  refine ⟨canonicalValuation bindings hloopFree hnonvariable, ?_⟩
  exact canonicalValuation_satisfies_of_classCoherent
    hloopFree hnonvariable
    (canonicalClassCoherent_of_reconciled
      hloopFree hnonvariable hreconciled)

private theorem solved_canonical_pair
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (leftRoot rightRoot : ClassAssignment bindings source.1)
    (hsmaller : ∀ target : DependencyNode bindings,
      DependencyOrder bindings target source →
      ∀ assignment : ClassAssignment bindings target.1,
        canonicalNodeValue bindings hloopFree hnonvariable target =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    :
    (∀ left right (_ : AtomSolved bindings left right),
      (∀ name, HumanMatchMergeSpec.AtomOccurs left name →
        AtomClassOccurs bindings leftRoot.1.2 name) →
      (∀ name, HumanMatchMergeSpec.AtomOccurs right name →
        AtomClassOccurs bindings rightRoot.1.2 name) →
      applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom left) =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom right)) ∧
    (∀ left right (_ : AtomsSolved bindings left right),
      (∀ atom, atom ∈ left → ∀ name,
        HumanMatchMergeSpec.AtomOccurs atom name →
        AtomClassOccurs bindings leftRoot.1.2 name) →
      (∀ atom, atom ∈ right → ∀ name,
        HumanMatchMergeSpec.AtomOccurs atom name →
        AtomClassOccurs bindings rightRoot.1.2 name) →
      (toLeaTTaAtoms left).map
          (applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)) =
        (toLeaTTaAtoms right).map
          (applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable))) := by
  apply solved_mutual_induction
  · intro name hleftRoot hrightRoot
    rfl
  · intro left right hclass hleftRoot hrightRoot
    obtain ⟨occurrence, hoccurs, hleftClass⟩ :=
      hleftRoot left (.var left)
    have hoccurrenceSupport := assignment_value_var_mem_bindingSupport
      leftRoot.2.1 hoccurs
    have hleftSupport := mem_bindingSupport_of_mem_eqClass
      hoccurrenceSupport hleftClass
    simpa [toLeaTTaAtom, applyClassSolution] using
      canonicalValuation_eq_of_mem_eqClass
        hloopFree hnonvariable hleftSupport hclass
  · intro left key right hassignment hclass hleftRoot hrightRoot
    obtain ⟨occurrence, hoccurs, hleftClass⟩ :=
      hleftRoot left (.var left)
    have hrepToOccurrence : occurrence ∈
        bindings.eqClass (bindings.eqRepresentative occurrence) :=
      mem_eqClass_symm
        (eqRepresentative_mem_eqClass bindings occurrence)
    have hkeyRep : key ∈
        bindings.eqClass (bindings.eqRepresentative occurrence) := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hrepToOccurrence hleftClass hclass ⊢
      exact (hrepToOccurrence.trans hleftClass).trans hclass
    let assignment :
        ClassAssignment bindings (bindings.eqRepresentative occurrence) :=
      ⟨(key, right), hassignment, hkeyRep⟩
    let target := chosenDependencyNode leftRoot hoccurs
    have hlt : DependencyOrder bindings target source :=
      chosenDependencyNode_lt leftRoot hnonvariable hoccurs
    have hleftValue := hsmaller target hlt assignment
    have hoccurrenceNode := canonicalValuation_eq_chosenDependencyNode
      hloopFree hnonvariable leftRoot hoccurs
    have hoccurrenceSupport := assignment_value_var_mem_bindingSupport
      leftRoot.2.1 hoccurs
    have hoccurrenceLeft := canonicalValuation_eq_of_mem_eqClass
      hloopFree hnonvariable hoccurrenceSupport hleftClass
    simpa [toLeaTTaAtom, applyClassSolution, target] using
      hoccurrenceLeft.symm.trans
        (hoccurrenceNode.trans hleftValue)
  · intro left key right hassignment hclass hleftRoot hrightRoot
    obtain ⟨occurrence, hoccurs, hrightClass⟩ :=
      hrightRoot right (.var right)
    have hrepToOccurrence : occurrence ∈
        bindings.eqClass (bindings.eqRepresentative occurrence) :=
      mem_eqClass_symm
        (eqRepresentative_mem_eqClass bindings occurrence)
    have hkeyRep : key ∈
        bindings.eqClass (bindings.eqRepresentative occurrence) := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hrepToOccurrence hrightClass hclass ⊢
      exact (hrepToOccurrence.trans hrightClass).trans hclass
    let assignment :
        ClassAssignment bindings (bindings.eqRepresentative occurrence) :=
      ⟨(key, left), hassignment, hkeyRep⟩
    let target := chosenDependencyNode rightRoot hoccurs
    have hlt : DependencyOrder bindings target source :=
      chosenDependencyNode_lt rightRoot hnonvariable hoccurs
    have hrightValue := hsmaller target hlt assignment
    have hoccurrenceNode := canonicalValuation_eq_chosenDependencyNode
      hloopFree hnonvariable rightRoot hoccurs
    have hoccurrenceSupport := assignment_value_var_mem_bindingSupport
      rightRoot.2.1 hoccurs
    have hoccurrenceRight := canonicalValuation_eq_of_mem_eqClass
      hloopFree hnonvariable hoccurrenceSupport hrightClass
    simpa [toLeaTTaAtom, applyClassSolution, target] using
      ((hoccurrenceRight.symm.trans
        (hoccurrenceNode.trans hrightValue))).symm
  · intro left key right hclass htail ih hleftRoot hrightRoot
    obtain ⟨occurrence, hoccurs, hleftClass⟩ :=
      hleftRoot left (.var left)
    have hkeyClass : key ∈ bindings.eqClass occurrence := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hleftClass hclass ⊢
      exact hleftClass.trans hclass
    have htailEq := ih
      (fun name hname => by
        cases hname
        exact ⟨occurrence, hoccurs, hkeyClass⟩)
      hrightRoot
    have hoccurrenceSupport := assignment_value_var_mem_bindingSupport
      leftRoot.2.1 hoccurs
    have hleftKey : canonicalValuation bindings hloopFree hnonvariable left =
        canonicalValuation bindings hloopFree hnonvariable key := by
      have hleftSupport := mem_bindingSupport_of_mem_eqClass
        hoccurrenceSupport hleftClass
      exact canonicalValuation_eq_of_mem_eqClass
        hloopFree hnonvariable hleftSupport hclass
    have htailEq' :
        canonicalValuation bindings hloopFree hnonvariable key =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom right) := by
      simpa [toLeaTTaAtom, applyClassSolution] using htailEq
    simpa [toLeaTTaAtom, applyClassSolution] using
      hleftKey.trans htailEq'
  · intro left key right hclass htail ih hleftRoot hrightRoot
    obtain ⟨occurrence, hoccurs, hrightClass⟩ :=
      hrightRoot right (.var right)
    have hkeyClass : key ∈ bindings.eqClass occurrence := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hrightClass hclass ⊢
      exact hrightClass.trans hclass
    have htailEq := ih hleftRoot
      (fun name hname => by
        cases hname
        exact ⟨occurrence, hoccurs, hkeyClass⟩)
    have hoccurrenceSupport := assignment_value_var_mem_bindingSupport
      rightRoot.2.1 hoccurs
    have hrightKey : canonicalValuation bindings hloopFree hnonvariable right =
        canonicalValuation bindings hloopFree hnonvariable key := by
      have hrightSupport := mem_bindingSupport_of_mem_eqClass
        hoccurrenceSupport hrightClass
      exact canonicalValuation_eq_of_mem_eqClass
        hloopFree hnonvariable hrightSupport hclass
    have htailEq' :
        applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom left) =
          canonicalValuation bindings hloopFree hnonvariable key := by
      simpa [toLeaTTaAtom, applyClassSolution] using htailEq
    simpa [toLeaTTaAtom, applyClassSolution] using
      htailEq'.trans hrightKey.symm
  · intro value hleftRoot hrightRoot
    rfl
  · intro left right hitems ih hleftRoot hrightRoot
    simp only [toLeaTTaAtom, applyClassSolution]
    congr 1
    exact ih
      (fun atom hatom name hoccurs =>
        hleftRoot name (.expression hatom hoccurs))
      (fun atom hatom name hoccurs =>
        hrightRoot name (.expression hatom hoccurs))
  · intro hleftRoot hrightRoot
    rfl
  · intro left right lefts rights hhead htail ihHead ihTail
      hleftRoot hrightRoot
    simp only [toLeaTTaAtoms, List.map_cons, List.cons.injEq]
    constructor
    · exact ihHead
        (fun name hoccurs => hleftRoot left (by simp) name hoccurs)
        (fun name hoccurs => hrightRoot right (by simp) name hoccurs)
    · exact ihTail
        (fun atom hatom => hleftRoot atom (by simp [hatom]))
        (fun atom hatom => hrightRoot atom (by simp [hatom]))

/-- A structural solution evaluates equally in the canonical valuation when
all assignment leaves below the two enclosing class values have already been
solved.  The latter premise is exactly the well-founded induction hypothesis
used by `canonicalClassCoherent_of_structurallySolved`. -/
theorem AtomSolved.canonical_eq_of_smaller
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (leftRoot rightRoot : ClassAssignment bindings source.1)
    (hsmaller : ∀ target : DependencyNode bindings,
      DependencyOrder bindings target source →
      ∀ assignment : ClassAssignment bindings target.1,
        canonicalNodeValue bindings hloopFree hnonvariable target =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right : Atom}
    (hsolved : AtomSolved bindings left right)
    (hleftRoot : ∀ name,
      HumanMatchMergeSpec.AtomOccurs left name →
      AtomClassOccurs bindings leftRoot.1.2 name)
    (hrightRoot : ∀ name,
      HumanMatchMergeSpec.AtomOccurs right name →
      AtomClassOccurs bindings rightRoot.1.2 name) :
    applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom left) =
      applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom right) :=
  (solved_canonical_pair hloopFree hnonvariable
    leftRoot rightRoot hsmaller).1 left right hsolved hleftRoot hrightRoot

/-- List companion of `AtomSolved.canonical_eq_of_smaller`. -/
theorem AtomsSolved.canonical_eq_of_smaller
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (leftRoot rightRoot : ClassAssignment bindings source.1)
    (hsmaller : ∀ target : DependencyNode bindings,
      DependencyOrder bindings target source →
      ∀ assignment : ClassAssignment bindings target.1,
        canonicalNodeValue bindings hloopFree hnonvariable target =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right : List Atom}
    (hsolved : AtomsSolved bindings left right)
    (hleftRoot : ∀ atom, atom ∈ left → ∀ name,
      HumanMatchMergeSpec.AtomOccurs atom name →
      AtomClassOccurs bindings leftRoot.1.2 name)
    (hrightRoot : ∀ atom, atom ∈ right → ∀ name,
      HumanMatchMergeSpec.AtomOccurs atom name →
      AtomClassOccurs bindings rightRoot.1.2 name) :
    (toLeaTTaAtoms left).map
        (applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)) =
      (toLeaTTaAtoms right).map
        (applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)) :=
  (solved_canonical_pair hloopFree hnonvariable
    leftRoot rightRoot hsmaller).2 left right hsolved hleftRoot hrightRoot

/-- A common structural root for every pair of values in one class is enough
to discharge canonical coherence.  The proof compares the chosen value and
the requested value separately with the root; it never assumes a transitivity
constructor for the syntactic certificate. -/
theorem canonicalClassCoherent_of_structurallyRooted
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hrooted : ClassAssignmentsStructurallyRooted bindings) :
    CanonicalClassCoherent bindings hloopFree hnonvariable := by
  unfold CanonicalClassCoherent
  intro source
  let NodeCoherent : DependencyNode bindings → Prop := fun node =>
    ∀ assignment : ClassAssignment bindings node.1,
      canonicalNodeValue bindings hloopFree hnonvariable node =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom assignment.1.2)
  change NodeCoherent source
  apply (dependencyOrder_wellFounded hloopFree).induction source
  intro source hsmaller assignment
  cases hchosen : chosenClassAssignment bindings source.1 with
  | none =>
      have hnonempty : Nonempty (ClassAssignment bindings source.1) :=
        ⟨assignment⟩
      simp [chosenClassAssignment, hnonempty] at hchosen
  | some chosen =>
      have hchosenToAssignment : assignment.1.1 ∈
          bindings.eqClass chosen.1.1 := by
        have hchosenClass := chosen.2.2
        have hassignmentClass := assignment.2.2
        rw [EqualityClosure.mem_eqClass_iff_reachable]
          at hchosenClass hassignmentClass ⊢
        exact hchosenClass.symm.trans hassignmentClass
      obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotToChosen,
          hpivotChosen, hpivotAssignment⟩ :=
        hrooted chosen.2.1 assignment.2.1 hchosenToAssignment
      have hpivotClass : pivotKey ∈ bindings.eqClass source.1 := by
        have hchosenClass := chosen.2.2
        rw [EqualityClosure.mem_eqClass_iff_reachable]
          at hchosenClass hpivotToChosen ⊢
        exact hchosenClass.trans hpivotToChosen
      let pivot : ClassAssignment bindings source.1 :=
        ⟨(pivotKey, pivotValue), hpivotMem, hpivotClass⟩
      have hpivotChosenEq :
          applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom pivotValue) =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom chosen.1.2) :=
        AtomSolved.canonical_eq_of_smaller hloopFree hnonvariable
          pivot chosen hsmaller hpivotChosen
          (fun name hoccurs => ⟨name, hoccurs,
            EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩)
          (fun name hoccurs => ⟨name, hoccurs,
            EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩)
      have hpivotAssignmentEq :
          applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom pivotValue) =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom assignment.1.2) :=
        AtomSolved.canonical_eq_of_smaller hloopFree hnonvariable
          pivot assignment hsmaller hpivotAssignment
          (fun name hoccurs => ⟨name, hoccurs,
            EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩)
          (fun name hoccurs => ⟨name, hoccurs,
            EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩)
      calc
        canonicalNodeValue bindings hloopFree hnonvariable source =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom chosen.1.2) :=
          canonicalNodeValue_eq_applyClassSolution_of_chosen
            hloopFree hnonvariable chosen hchosen
        _ = applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom assignment.1.2) :=
          hpivotChosenEq.symm.trans hpivotAssignmentEq

/-- A loop-free, non-variable record with rooted structural reconciliation has
a concrete canonical model. -/
theorem has_model_of_structurallyRooted
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hrooted : ClassAssignmentsStructurallyRooted bindings) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings := by
  refine ⟨canonicalValuation bindings hloopFree hnonvariable, ?_⟩
  exact canonicalValuation_satisfies_of_classCoherent
    hloopFree hnonvariable
    (canonicalClassCoherent_of_structurallyRooted
      hloopFree hnonvariable hrooted)

/-- Structural class-value reconciliation is precisely strong enough to
discharge the canonical model's remaining coherence obligation. -/
theorem canonicalClassCoherent_of_structurallySolved
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hsolved : ClassAssignmentsStructurallySolved bindings) :
    CanonicalClassCoherent bindings hloopFree hnonvariable := by
  unfold CanonicalClassCoherent
  intro source
  let NodeCoherent : DependencyNode bindings → Prop := fun node =>
    ∀ assignment : ClassAssignment bindings node.1,
      canonicalNodeValue bindings hloopFree hnonvariable node =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom assignment.1.2)
  change NodeCoherent source
  apply (dependencyOrder_wellFounded hloopFree).induction source
  intro source hsmaller assignment
  cases hchosen : chosenClassAssignment bindings source.1 with
  | none =>
      have hnonempty : Nonempty (ClassAssignment bindings source.1) :=
        ⟨assignment⟩
      simp [chosenClassAssignment, hnonempty] at hchosen
  | some chosen =>
      have hchosenToAssignment : assignment.1.1 ∈
          bindings.eqClass chosen.1.1 := by
        have hchosenClass := chosen.2.2
        have hassignmentClass := assignment.2.2
        rw [EqualityClosure.mem_eqClass_iff_reachable]
          at hchosenClass hassignmentClass ⊢
        exact hchosenClass.symm.trans hassignmentClass
      calc
        canonicalNodeValue bindings hloopFree hnonvariable source =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom chosen.1.2) :=
          canonicalNodeValue_eq_applyClassSolution_of_chosen
            hloopFree hnonvariable chosen hchosen
        _ = applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom assignment.1.2) :=
          AtomSolved.canonical_eq_of_smaller hloopFree hnonvariable
            chosen assignment hsmaller
            (hsolved chosen.2.1 assignment.2.1 hchosenToAssignment)
            (fun name hoccurs => ⟨name, hoccurs,
              EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩)
            (fun name hoccurs => ⟨name, hoccurs,
              EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩)

/-- A loop-free, non-variable record whose raw class assignments carry the
structural reconciliation certificate has a concrete canonical model. -/
theorem has_model_of_structurallySolved
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hsolved : ClassAssignmentsStructurallySolved bindings) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings := by
  refine ⟨canonicalValuation bindings hloopFree hnonvariable, ?_⟩
  exact canonicalValuation_satisfies_of_classCoherent
    hloopFree hnonvariable
    (canonicalClassCoherent_of_structurallySolved
      hloopFree hnonvariable hsolved)

/-- Positive rooted canary: a singleton class uses its only stored value as
the reconciliation root. -/
theorem structuralSolvedProbe_rooted :
    ClassAssignmentsStructurallyRooted structuralSolvedProbe := by
  apply structurallyRooted_of_structurallySolved
  exact structurallySolved_assign_of_classValues_nil
    (bindings := Bindings.empty) (key := "y") (value := .symbol "a")
    (by
      intro leftKey rightKey leftValue rightValue hleft
      simp [Bindings.empty] at hleft)
    (by simp [AssignmentsNodup, Bindings.empty])
    rfl

/-- Positive reconciliation canary: the singleton class selects its only
stored value as the directional pivot. -/
theorem structuralSolvedProbe_reconciled :
    ClassAssignmentsReconciled structuralSolvedProbe := by
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  have hleftEq : leftKey = "y" ∧ leftValue = .symbol "a" := by
    simpa [structuralSolvedProbe, Bindings.assign,
      Bindings.isBound, Bindings.lookup, Bindings.empty] using hleft
  have hrightEq : rightKey = "y" ∧ rightValue = .symbol "a" := by
    simpa [structuralSolvedProbe, Bindings.assign,
      Bindings.isBound, Bindings.lookup, Bindings.empty] using hright
  rcases hleftEq with ⟨rfl, rfl⟩
  rcases hrightEq with ⟨rfl, rfl⟩
  exact ⟨"y", .symbol "a", hleft,
    EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl,
    AtomReconciled.refl structuralSolvedProbe (.symbol "a"),
    AtomReconciled.refl structuralSolvedProbe (.symbol "a")⟩

/-- Negative rooted canary: loop freedom cannot turn two unreconciled class
values into a common structural solution. -/
theorem incompatibleAcyclicProbe_not_structurallyRooted :
    ¬ClassAssignmentsStructurallyRooted incompatibleAcyclicProbe := by
  intro hrooted
  apply incompatibleAcyclicProbe_has_no_model
  exact has_model_of_structurallyRooted
    incompatibleAcyclicProbe_loopFree
    incompatibleAcyclicProbe_nonvariable hrooted

/-- Negative reconciliation canary: dependency acyclicity cannot manufacture
a directional root for incompatible class values. -/
theorem incompatibleAcyclicProbe_not_reconciled :
    ¬ClassAssignmentsReconciled incompatibleAcyclicProbe := by
  intro hreconciled
  apply incompatibleAcyclicProbe_has_no_model
  exact has_model_of_reconciled
    incompatibleAcyclicProbe_loopFree
    incompatibleAcyclicProbe_nonvariable hreconciled

/-! ## Strictly-below reconciliation paths

`AtomReconciled` deliberately has no transitivity constructor.  Unrestricted
transitivity would be unsound for the canonical model: in an incoherent class,
two incompatible values can both be connected through a variable in that same
class.  Recursive matcher/merge composition nevertheless needs a transitive
operation.  The correct index is the ambient dependency class: every atom at
every join point must depend only on classes strictly below it.
-/

private theorem reconciled_symm_pair
    {bindings : Bindings} :
    (∀ left right (_ : AtomReconciled bindings left right),
      AtomReconciled bindings right left) ∧
    (∀ left right (_ : AtomsReconciled bindings left right),
      AtomsReconciled bindings right left) := by
  apply reconciled_mutual_induction
  · intro name
    exact .symbol name
  · intro left right hclass
    exact .varVar (mem_eqClass_symm hclass)
  · intro left key stored right hassignment hclass htail ih
    exact .assignedRight hassignment hclass ih
  · intro left stored key right hassignment hclass htail ih
    exact .assignedLeft hassignment hclass ih
  · intro value
    exact .grounded value
  · intro left right hitems ih
    exact .expression ih
  · exact .nil
  · intro left right lefts rights hhead htail ihHead ihTail
    exact .cons ihHead ihTail

/-- Directional reconciliation can be reversed without adding an unguarded
transitivity principle. -/
theorem AtomReconciled.symm
    {bindings : Bindings} {left right : Atom}
    (hreconciled : AtomReconciled bindings left right) :
    AtomReconciled bindings right left :=
  (reconciled_symm_pair).1 left right hreconciled

/-- List companion of `AtomReconciled.symm`. -/
theorem AtomsReconciled.symm
    {bindings : Bindings} {left right : List Atom}
    (hreconciled : AtomsReconciled bindings left right) :
    AtomsReconciled bindings right left :=
  (reconciled_symm_pair).2 left right hreconciled

/-- A composable reconciliation path below one ambient dependency class.
Unlike a bare transitive closure, every endpoint and intermediate is guarded
by `AtomDependenciesBelow`.  The expression constructors are the congruence
closure needed to assemble independently reconciled expression children. -/
inductive AtomReconciliationPath
    (bindings : Bindings) (source : DependencyNode bindings) :
    Atom → Atom → Prop where
  | step {left right : Atom} :
      AtomDependenciesBelow bindings source left →
      AtomReconciled bindings left right →
      AtomDependenciesBelow bindings source right →
      AtomReconciliationPath bindings source left right
  | trans {left middle right : Atom} :
      AtomReconciliationPath bindings source left middle →
      AtomReconciliationPath bindings source middle right →
      AtomReconciliationPath bindings source left right
  | expressionNil :
      AtomReconciliationPath bindings source
        (.expression []) (.expression [])
  | expressionCons {left right : Atom} {lefts rights : List Atom} :
      AtomReconciliationPath bindings source left right →
      AtomReconciliationPath bindings source
        (.expression lefts) (.expression rights) →
      AtomReconciliationPath bindings source
        (.expression (left :: lefts))
        (.expression (right :: rights))

/-- Every strictly-below atom has the reflexive reconciliation path. -/
theorem AtomReconciliationPath.refl
    {bindings : Bindings} {source : DependencyNode bindings}
    {atom : Atom}
    (hbelow : AtomDependenciesBelow bindings source atom) :
    AtomReconciliationPath bindings source atom atom :=
  .step hbelow (AtomReconciled.refl bindings atom) hbelow

/-- Strictly-below reconciliation paths are symmetric. -/
theorem AtomReconciliationPath.symm
    {bindings : Bindings} {source : DependencyNode bindings}
    {left right : Atom}
    (hpath : AtomReconciliationPath bindings source left right) :
    AtomReconciliationPath bindings source right left := by
  induction hpath with
  | step hleft hreconciled hright =>
      exact .step hright hreconciled.symm hleft
  | trans hleft hright ihLeft ihRight =>
      exact .trans ihRight ihLeft
  | expressionNil => exact .expressionNil
  | expressionCons _ _ ihHead ihTail =>
      exact .expressionCons ihHead ihTail

/-- A guarded path can be reindexed by any other name in the same ambient
equality class. -/
theorem AtomReconciliationPath.of_source_mem_eqClass
    {bindings : Bindings} {source replacement : DependencyNode bindings}
    {left right : Atom}
    (hpath : AtomReconciliationPath bindings source left right)
    (hclass : replacement.1 ∈ bindings.eqClass source.1) :
    AtomReconciliationPath bindings replacement left right := by
  induction hpath with
  | step hleft hreconciled hright =>
      exact .step
        (hleft.of_source_mem_eqClass hclass)
        hreconciled
        (hright.of_source_mem_eqClass hclass)
  | trans _ _ ihLeft ihRight =>
      exact .trans ihLeft ihRight
  | expressionNil => exact .expressionNil
  | expressionCons _ _ ihHead ihTail =>
      exact .expressionCons ihHead ihTail

/-- A strictly-below path evaluates equally in the canonical valuation. -/
theorem AtomReconciliationPath.canonical_eq
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    {source : DependencyNode bindings}
    (hsmaller : ∀ target : DependencyNode bindings,
      DependencyOrder bindings target source →
      ∀ assignment : ClassAssignment bindings target.1,
        canonicalNodeValue bindings hloopFree hnonvariable target =
          applyClassSolution
            (canonicalValuation bindings hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right : Atom}
    (hpath : AtomReconciliationPath bindings source left right) :
    applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom left) =
      applyClassSolution
        (canonicalValuation bindings hloopFree hnonvariable)
        (toLeaTTaAtom right) := by
  induction hpath with
  | step hleft hreconciled hright =>
      exact AtomReconciled.canonical_eq_of_below
        hloopFree hnonvariable hsmaller hreconciled hleft hright
  | trans _ _ ihLeft ihRight =>
      exact ihLeft.trans ihRight
  | expressionNil => rfl
  | expressionCons _ _ ihHead ihTail =>
      simpa [toLeaTTaAtom, applyClassSolution] using
        congrArg₂ List.cons ihHead
          (by
            simpa [toLeaTTaAtom, applyClassSolution] using ihTail)

/-! ## Backward guarded presentation

Reconciliation may consume a proposed assignment without retaining it as a
literal record entry.  The right invariant therefore says that the eventual
target *presents* every source assignment by a guarded path, while retaining
the source equality closure literally.  This is the backward-facing interface
needed to recover the equations discharged by recursive match/merge-back. -/

/-- Every occurrence in an expression inherits the expression's dependency
bound. -/
theorem AtomDependenciesBelow.of_mem_expression
    {bindings : Bindings} {source : DependencyNode bindings}
    {atoms : List Atom} {atom : Atom}
    (hbelow : AtomDependenciesBelow bindings source (.expression atoms))
    (hmem : atom ∈ atoms) :
    AtomDependenciesBelow bindings source atom := by
  intro name hoccurs
  exact hbelow name (.expression hmem hoccurs)

/-- A variable may be renamed within its equality class without changing its
strict dependency bound. -/
theorem AtomDependenciesBelow.var_of_mem_eqClass
    {bindings : Bindings} {source : DependencyNode bindings}
    {left right : String}
    (hbelow : AtomDependenciesBelow bindings source (.var left))
    (hclass : right ∈ bindings.eqClass left) :
    AtomDependenciesBelow bindings source (.var right) := by
  intro name hoccurs
  cases hoccurs with
  | var =>
      obtain ⟨hleftSupport, hlt⟩ := hbelow left (.var left)
      let hrightSupport : right ∈ bindingSupport bindings :=
        mem_bindingSupport_of_mem_eqClass hleftSupport hclass
      refine ⟨hrightSupport, ?_⟩
      simpa [representativeNode,
        eqRepresentative_eq_of_mem_eqClass hclass] using hlt

/-- One atom equation is presented in a target when it has a guarded path
below every ambient class below which both endpoints live. -/
def AtomPathPresented (target : Bindings) (left right : Atom) : Prop :=
  ∀ (source : DependencyNode target),
    AtomDependenciesBelow target source left →
    AtomDependenciesBelow target source right →
      AtomReconciliationPath target source left right

/-- Pointwise list companion of `AtomPathPresented`. -/
inductive AtomsPathPresented (target : Bindings) :
    List Atom → List Atom → Prop where
  | nil : AtomsPathPresented target [] []
  | cons {left right : Atom} {lefts rights : List Atom} :
      AtomPathPresented target left right →
      AtomsPathPresented target lefts rights →
      AtomsPathPresented target (left :: lefts) (right :: rights)

/-- Guarded atom presentation is symmetric. -/
theorem AtomPathPresented.symm
    {target : Bindings} {left right : Atom}
    (hpresented : AtomPathPresented target left right) :
    AtomPathPresented target right left := by
  intro source hright hleft
  exact (hpresented source hleft hright).symm

/-- Guarded atom presentation composes when the shared intermediate is known
to lie below the same ambient dependency class. -/
theorem AtomPathPresented.trans_of_middle
    {target : Bindings} {left middle right : Atom}
    (hleft : AtomPathPresented target left middle)
    (hright : AtomPathPresented target middle right)
    (hmiddle : ∀ (source : DependencyNode target),
      AtomDependenciesBelow target source left →
      AtomDependenciesBelow target source right →
        AtomDependenciesBelow target source middle) :
    AtomPathPresented target left right := by
  intro source hleftBelow hrightBelow
  have hmiddleBelow := hmiddle source hleftBelow hrightBelow
  exact .trans
    (hleft source hleftBelow hmiddleBelow)
    (hright source hmiddleBelow hrightBelow)

/-- A replicated pivot presentation exposes one guarded path to every
right-hand list element. -/
theorem AtomsPathPresented.each_of_replicate
    {target : Bindings} {pivot : Atom} {values : List Atom}
    (hpresented : AtomsPathPresented target
      (List.replicate values.length pivot) values) :
    ∀ value ∈ values, AtomPathPresented target pivot value := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons, List.replicate_succ] at hpresented
      cases hpresented with
      | cons hhead htail =>
          intro candidate hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact ih htail candidate hmem

/-- Pointwise guarded paths assemble under the expression constructor. -/
theorem AtomsPathPresented.expressionPath
    {target : Bindings} {left right : List Atom}
    (hpaths : AtomsPathPresented target left right)
    (source : DependencyNode target)
    (hleft : AtomDependenciesBelow target source (.expression left))
    (hright : AtomDependenciesBelow target source (.expression right)) :
    AtomReconciliationPath target source
      (.expression left) (.expression right) := by
  induction hpaths with
  | nil => exact .expressionNil
  | @cons left right lefts rights hhead htail ih =>
      apply AtomReconciliationPath.expressionCons
      · exact hhead source
          (hleft.of_mem_expression (by simp))
          (hright.of_mem_expression (by simp))
      · exact ih
          (fun name hoccurs => by
            cases hoccurs with
            | expression hmem hinner =>
                exact hleft name (.expression (by simp [hmem]) hinner))
          (fun name hoccurs => by
            cases hoccurs with
            | expression hmem hinner =>
                exact hright name (.expression (by simp [hmem]) hinner))

/-- A target presents a source binding record when every source assignment is
realized by a guarded path and the source equality closure embeds literally in
the target closure. -/
structure BindingPathPresentation (target source : Bindings) : Prop where
  assignments : ∀ key value,
    (key, value) ∈ source.assignments →
      AtomPathPresented target (.var key) value
  classes : ∀ {left right},
    right ∈ source.eqClass left → right ∈ target.eqClass left

/-- Every binding record guardedly presents itself. -/
theorem BindingPathPresentation.refl (bindings : Bindings) :
    BindingPathPresentation bindings bindings where
  assignments _key value hmem _source hkey hvalue :=
    .step hkey
      (.assignedLeft hmem
        (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
        (AtomReconciled.refl bindings value))
      hvalue
  classes hclass := hclass

/-- Literal inclusion supplies a guarded presentation. -/
theorem BindingPathPresentation.of_subrecord
    {source target : Bindings}
    (hsubrecord : BindingSubrecord source target) :
    BindingPathPresentation target source where
  assignments _key value hmem _sourceNode hkey hvalue :=
    .step hkey
      (.assignedLeft (hsubrecord.1 _ hmem)
        (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
        (AtomReconciled.refl target value))
      hvalue
  classes hclass := hsubrecord.mem_eqClass hclass

/-- A presentation restricts along a literal source subrecord. -/
theorem BindingPathPresentation.of_source_subrecord
    {target source before : Bindings}
    (hpresentation : BindingPathPresentation target source)
    (hbefore : BindingSubrecord before source) :
    BindingPathPresentation target before where
  assignments key value hmem :=
    hpresentation.assignments key value (hbefore.1 _ hmem)
  classes hclass := hpresentation.classes (hbefore.mem_eqClass hclass)

/-- A value visible in a source equality class is guardedly presented from
every variable naming that class. -/
theorem BindingPathPresentation.path_of_mem_classValues
    {target source : Bindings} {key : String} {value : Atom}
    (hpresentation : BindingPathPresentation target source)
    (hvalue : value ∈ source.classValues key) :
    AtomPathPresented target (.var key) value := by
  obtain ⟨storedKey, hstored, hstoredClass⟩ :=
    exists_assignment_of_mem_classValues hvalue
  have htargetClass : storedKey ∈ target.eqClass key :=
    hpresentation.classes hstoredClass
  intro ambient hkeyBelow hvalueBelow
  have hstoredBelow :=
    hkeyBelow.var_of_mem_eqClass htargetClass
  exact .trans
    (.step hkeyBelow (.varVar htargetClass) hstoredBelow)
    (hpresentation.assignments storedKey value hstored
      ambient hstoredBelow hvalueBelow)

/-- The edge requested by `addEquality` belongs to the resulting equality
class, including the reflexive case. -/
private theorem addEquality_right_mem_eqClass
    (bindings : Bindings) (left right : String) :
    right ∈ (bindings.addEquality left right).eqClass left := by
  rw [EqualityClosure.mem_eqClass_iff_reachable]
  by_cases hsame : left = right
  · subst right
    exact .rfl
  · exact (show
        (EqualityClosure.edgeGraph
          (bindings.addEquality left right).equalities).Adj left right by
      rw [EqualityClosure.edgeGraph_adj_iff]
      exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable

/-- One neutral constraint presented in an eventual target. -/
def ConstraintPathPresented (target : Bindings) :
    HumanMatchMergeSpec.Constraint → Prop
  | .value key value => AtomPathPresented target (.var key) value
  | .equality left right => right ∈ target.eqClass left

/-- Every constraint in a fold order is presented in an eventual target. -/
def ConstraintsPathPresented (target : Bindings)
    (constraints : List HumanMatchMergeSpec.Constraint) : Prop :=
  ∀ constraint ∈ constraints, ConstraintPathPresented target constraint

/-- A solved permutation of a binding record's neutral constraints gives its
guarded presentation. -/
theorem BindingPathPresentation.of_constraintsPresented
    {source target : Bindings}
    {order : List HumanMatchMergeSpec.Constraint}
    (horder : order.Perm (HumanMatchMergeSpec.constraints source))
    (hpresented : ConstraintsPathPresented target order) :
    BindingPathPresentation target source where
  assignments key value hmem := by
    apply hpresented (.value key value)
    exact (List.Perm.mem_iff horder).mpr
      (HumanMatchSolutionTheory.value_mem_constraints_iff.mpr hmem)
  classes := eqClass_mono_of_equalities_solved fun left right hmem => by
    apply hpresented (.equality left right)
    exact (List.Perm.mem_iff horder).mpr
      (HumanMatchSolutionTheory.equality_mem_constraints_iff.mpr hmem)

/-- Every pair of class assignments is joined to a stored pivot by paths that
remain strictly below the class being reconciled. -/
def ClassAssignmentsPathReconciled (bindings : Bindings) : Prop :=
  ∀ (source : DependencyNode bindings)
    (left right : ClassAssignment bindings source.1),
    ∃ pivot : ClassAssignment bindings source.1,
      AtomReconciliationPath bindings source pivot.1.2 left.1.2 ∧
      AtomReconciliationPath bindings source pivot.1.2 right.1.2

/-- Fixed-target continuation form of guarded class reconciliation.  Every
source constraint occurs literally in the final target, while the common
pivot and both paths are chosen in that final target.  This is the form needed
to traverse a merge derivation whose transient proposed constraints need not
survive as raw assignments. -/
structure ClassAssignmentsPathReconciledIn
    (target source : Bindings) : Prop where
  subrecord : BindingSubrecord source target
  paths : ∀ {leftKey rightKey : String} {leftValue rightValue : Atom}
      (hleft : (leftKey, leftValue) ∈ source.assignments)
      (_hright : (rightKey, rightValue) ∈ source.assignments)
      (_hclass : rightKey ∈ source.eqClass leftKey),
    let leftTarget : (leftKey, leftValue) ∈ target.assignments :=
      subrecord.1 _ hleft
    let sourceNode : DependencyNode target :=
      ⟨leftKey, assignment_key_mem_bindingSupport leftTarget⟩
    ∃ pivot : ClassAssignment target leftKey,
      AtomReconciliationPath target sourceNode pivot.1.2 leftValue ∧
      AtomReconciliationPath target sourceNode pivot.1.2 rightValue

/-- A final guarded certificate supplies its fixed-target continuation form. -/
theorem ClassAssignmentsPathReconciled.toIn
    {bindings : Bindings}
    (hreconciled : ClassAssignmentsPathReconciled bindings) :
    ClassAssignmentsPathReconciledIn bindings bindings where
  subrecord := BindingSubrecord.refl bindings
  paths := by
    intro leftKey rightKey leftValue rightValue hleft hright hclass
    dsimp
    let source : DependencyNode bindings :=
      ⟨leftKey, assignment_key_mem_bindingSupport hleft⟩
    let left : ClassAssignment bindings source.1 :=
      ⟨(leftKey, leftValue), hleft,
        EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩
    let right : ClassAssignment bindings source.1 :=
      ⟨(rightKey, rightValue), hright, hclass⟩
    exact hreconciled source left right

/-- The fixed-target continuation at the final record is equivalent to the
public guarded certificate. -/
theorem ClassAssignmentsPathReconciledIn.toFinal
    {bindings : Bindings}
    (hreconciled : ClassAssignmentsPathReconciledIn bindings bindings) :
    ClassAssignmentsPathReconciled bindings := by
  intro source left right
  have hrightToLeft : right.1.1 ∈ bindings.eqClass left.1.1 := by
    have hleftClass := left.2.2
    have hrightClass := right.2.2
    rw [EqualityClosure.mem_eqClass_iff_reachable]
      at hleftClass hrightClass ⊢
    exact hleftClass.symm.trans hrightClass
  obtain ⟨pivot, hpivotLeft, hpivotRight⟩ :=
    hreconciled.paths left.2.1 right.2.1 hrightToLeft
  let leftNode : DependencyNode bindings :=
    ⟨left.1.1, assignment_key_mem_bindingSupport left.2.1⟩
  have hsourceClass : source.1 ∈ bindings.eqClass leftNode.1 := by
    change source.1 ∈ bindings.eqClass left.1.1
    exact mem_eqClass_symm left.2.2
  have hpivotClass : pivot.1.1 ∈ bindings.eqClass source.1 := by
    have hpivotToLeft := pivot.2.2
    have hleftToSource := left.2.2
    rw [EqualityClosure.mem_eqClass_iff_reachable]
      at hpivotToLeft hleftToSource ⊢
    exact hleftToSource.trans hpivotToLeft
  let finalPivot : ClassAssignment bindings source.1 :=
    ⟨pivot.1, pivot.2.1, hpivotClass⟩
  exact ⟨finalPivot,
    hpivotLeft.of_source_mem_eqClass hsourceClass,
    hpivotRight.of_source_mem_eqClass hsourceClass⟩

/-- The empty accumulator is guarded-reconciled in every fixed final target. -/
theorem pathReconciledIn_empty (target : Bindings) :
    ClassAssignmentsPathReconciledIn target Bindings.empty where
  subrecord := by
    constructor
    · intro assignment hmem
      simp [Bindings.empty] at hmem
    · intro equality hmem
      simp [Bindings.empty] at hmem
  paths := by
    intro leftKey rightKey leftValue rightValue hleft
    simp [Bindings.empty] at hleft

/-- Fixed-target reconciliation restricts to every literal source subrecord. -/
theorem ClassAssignmentsPathReconciledIn.of_source_subrecord
    {target source before : Bindings}
    (hreconciled : ClassAssignmentsPathReconciledIn target source)
    (hbefore : BindingSubrecord before source) :
    ClassAssignmentsPathReconciledIn target before where
  subrecord := hbefore.trans hreconciled.subrecord
  paths := by
    intro leftKey rightKey leftValue rightValue hleft hright hclass
    dsimp
    have hleftSource := hbefore.1 _ hleft
    have hrightSource := hbefore.1 _ hright
    have hclassSource := hbefore.mem_eqClass hclass
    exact hreconciled.paths hleftSource hrightSource hclassSource

/-- Adding the first assignment in a class preserves a fixed-final-target
guarded certificate. -/
theorem pathReconciledIn_assign_of_classValues_nil
    {target bindings : Bindings} {key : String} {value : Atom}
    (hreconciled : ClassAssignmentsPathReconciledIn target bindings)
    (htargetNonvariable : AssignmentsNonVariable target)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : bindings.classValues key = [])
    (hout : BindingSubrecord (bindings.assign key value) target) :
    ClassAssignmentsPathReconciledIn target
      (bindings.assign key value) := by
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  dsimp
  have hbound := isBound_false_of_classValues_nil hvalues
  have hleftCases :
      (leftKey, leftValue) ∈ bindings.assignments ∨
        (leftKey = key ∧ leftValue = value) := by
    simpa [Bindings.assign, hbound] using hleft
  have hrightCases :
      (rightKey, rightValue) ∈ bindings.assignments ∨
        (rightKey = key ∧ rightValue = value) := by
    simpa [Bindings.assign, hbound] using hright
  have hclassOld : rightKey ∈ bindings.eqClass leftKey := by
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  rcases hleftCases with hleftOld | hleftNew
  · rcases hrightCases with hrightOld | hrightNew
    · obtain ⟨pivot, hpivotLeft, hpivotRight⟩ :=
        hreconciled.paths hleftOld hrightOld hclassOld
      exact ⟨pivot, hpivotLeft, hpivotRight⟩
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      have hleftClass : leftKey ∈ bindings.eqClass key := by
        rw [hrightKey] at hclassOld
        exact mem_eqClass_symm hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hleftOld hleftClass
      rw [hvalues] at hvisible
      simp at hvisible
  · rcases hleftNew with ⟨hleftKey, hleftValue⟩
    rcases hrightCases with hrightOld | hrightNew
    · have hrightClass : rightKey ∈ bindings.eqClass key := by
        simpa [hleftKey] using hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hrightOld hrightClass
      rw [hvalues] at hvisible
      simp at hvisible
    · rcases hrightNew with ⟨hrightKey, hrightValue⟩
      subst leftKey
      subst leftValue
      subst rightKey
      subst rightValue
      let htargetMem : (key, value) ∈ target.assignments :=
        hout.1 _ hleft
      let source : DependencyNode target :=
        ⟨key, assignment_key_mem_bindingSupport htargetMem⟩
      let pivot : ClassAssignment target source.1 :=
        ⟨(key, value), htargetMem,
          EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩
      have hbelow :=
        ClassAssignment.value_dependenciesBelow_source
          htargetNonvariable pivot
      exact ⟨pivot, .refl hbelow, .refl hbelow⟩

/-- Joining two classes whose visible values literally agree preserves the
fixed-final-target guarded certificate. -/
theorem pathReconciledIn_addEquality_of_valuesAgree
    {target bindings : Bindings} {left right : String}
    (hreconciled : ClassAssignmentsPathReconciledIn target bindings)
    (htargetNonvariable : AssignmentsNonVariable target)
    (hnodup : AssignmentsNodup bindings)
    (hagree : HumanMatchMergeSpec.ValuesAgree
      ((bindings.addEquality left right).classValues left))
    (hout : BindingSubrecord (bindings.addEquality left right) target) :
    ClassAssignmentsPathReconciledIn target
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  dsimp
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hvalueEq := valuesAgree_eq_of_mem
      hagree hleftVisible hrightVisible
    subst rightValue
    let htargetMem : (leftKey, leftValue) ∈ target.assignments :=
      hout.1 _ hleft
    let source : DependencyNode target :=
      ⟨leftKey, assignment_key_mem_bindingSupport htargetMem⟩
    let pivot : ClassAssignment target source.1 :=
      ⟨(leftKey, leftValue), htargetMem,
        EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl⟩
    have hbelow :=
      ClassAssignment.value_dependenciesBelow_source
        htargetNonvariable pivot
    exact ⟨pivot, .refl hbelow, .refl hbelow⟩
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    obtain ⟨pivot, hpivotLeft, hpivotRight⟩ :=
      hreconciled.paths hleftOld hrightOld hclassOld
    exact ⟨pivot, hpivotLeft, hpivotRight⟩

/-- A joined class is guarded-reconciled when a visible pivot has a guarded
path to every visible value.  The callback is indexed by the eventual target
class name, making it directly usable after recursive match/merge-back. -/
theorem pathReconciledIn_addEquality_of_pivotPaths
    {target bindings : Bindings} {left right : String}
    {first : Atom} {rest : List Atom}
    (hreconciled : ClassAssignmentsPathReconciledIn target bindings)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : (first :: rest).Perm
      ((bindings.addEquality left right).classValues left))
    (hout : BindingSubrecord (bindings.addEquality left right) target)
    (hpivotPaths : ∀ (source : DependencyNode target),
      source.1 ∈ target.eqClass left →
      ∀ value ∈ first :: rest,
        AtomReconciliationPath target source first value) :
    ClassAssignmentsPathReconciledIn target
      (bindings.addEquality left right) := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  have hfirstVisible : first ∈ candidate.classValues left := by
    exact (List.Perm.mem_iff hvalues).mp (by simp)
  obtain ⟨pivotKey, hpivotMem, hpivotJoined⟩ :=
    exists_assignment_of_mem_classValues hfirstVisible
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass
  dsimp
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hleftList : leftValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hleftVisible
    have hrightList : rightValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hrightVisible
    let hpivotTarget : (pivotKey, first) ∈ target.assignments :=
      hout.1 _ (by simpa [candidate] using hpivotMem)
    let source : DependencyNode target :=
      ⟨leftKey, assignment_key_mem_bindingSupport
        (hout.1 _ hleft)⟩
    have hpivotClassCandidate : pivotKey ∈ candidate.eqClass leftKey := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hpivotJoined hjoined ⊢
      exact hjoined.symm.trans hpivotJoined
    have hpivotClass : pivotKey ∈ target.eqClass source.1 :=
      hout.mem_eqClass hpivotClassCandidate
    let pivot : ClassAssignment target source.1 :=
      ⟨(pivotKey, first), hpivotTarget, hpivotClass⟩
    have hsourceJoined : source.1 ∈ target.eqClass left :=
      hout.mem_eqClass hjoined
    exact ⟨pivot,
      hpivotPaths source hsourceJoined leftValue hleftList,
      hpivotPaths source hsourceJoined rightValue hrightList⟩
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    obtain ⟨pivot, hpivotLeft, hpivotRight⟩ :=
      hreconciled.paths hleftOld hrightOld hclassOld
    exact ⟨pivot, hpivotLeft, hpivotRight⟩

/-- The earlier common-root certificate is a special case of guarded path
reconciliation.  The path form is strictly more compositional, while all
three endpoints are below the ambient class because they are stored class
assignments. -/
theorem ClassAssignmentsReconciled.toPathReconciled
    {bindings : Bindings}
    (hnonvariable : AssignmentsNonVariable bindings)
    (hreconciled : ClassAssignmentsReconciled bindings) :
    ClassAssignmentsPathReconciled bindings := by
  intro source left right
  have hrightToLeft : right.1.1 ∈ bindings.eqClass left.1.1 := by
    have hleftClass := left.2.2
    have hrightClass := right.2.2
    rw [EqualityClosure.mem_eqClass_iff_reachable]
      at hleftClass hrightClass ⊢
    exact hleftClass.symm.trans hrightClass
  obtain ⟨pivotKey, pivotValue, hpivotMem, hpivotToLeft,
      hpivotLeft, hpivotRight⟩ :=
    hreconciled left.2.1 right.2.1 hrightToLeft
  have hpivotClass : pivotKey ∈ bindings.eqClass source.1 := by
    have hleftClass := left.2.2
    rw [EqualityClosure.mem_eqClass_iff_reachable]
      at hleftClass hpivotToLeft ⊢
    exact hleftClass.trans hpivotToLeft
  let pivot : ClassAssignment bindings source.1 :=
    ⟨(pivotKey, pivotValue), hpivotMem, hpivotClass⟩
  have hpivotBelow :=
    ClassAssignment.value_dependenciesBelow_source hnonvariable pivot
  have hleftBelow :=
    ClassAssignment.value_dependenciesBelow_source hnonvariable left
  have hrightBelow :=
    ClassAssignment.value_dependenciesBelow_source hnonvariable right
  exact ⟨pivot,
    .step hpivotBelow hpivotLeft hleftBelow,
    .step hpivotBelow hpivotRight hrightBelow⟩

/-- Classes carrying at most one raw assignment are the conflict-free base of
guarded reconciliation. -/
theorem pathReconciled_of_subsingleton_classAssignments
    {bindings : Bindings}
    (hnonvariable : AssignmentsNonVariable bindings)
    (hsubsingleton : ∀ source : DependencyNode bindings,
      Subsingleton (ClassAssignment bindings source.1)) :
    ClassAssignmentsPathReconciled bindings := by
  intro source left right
  have hright : right = left :=
    @Subsingleton.elim _ (hsubsingleton source) right left
  subst right
  have hbelow :=
    ClassAssignment.value_dependenciesBelow_source hnonvariable left
  exact ⟨left, .refl hbelow, .refl hbelow⟩

/-- A binding list with at most one raw assignment has at most one assignment
in every equality class. -/
theorem classAssignments_subsingleton_of_assignments_unique
    {bindings : Bindings}
    (hunique : ∀ left ∈ bindings.assignments,
      ∀ right ∈ bindings.assignments, left = right) :
    ∀ source : DependencyNode bindings,
      Subsingleton (ClassAssignment bindings source.1) := by
  intro source
  constructor
  intro left right
  apply Subtype.ext
  exact hunique left.1 left.2.1 right.1 right.2.1

/-- Strictly-below path provenance discharges canonical class coherence. -/
theorem canonicalClassCoherent_of_pathReconciled
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hreconciled : ClassAssignmentsPathReconciled bindings) :
    CanonicalClassCoherent bindings hloopFree hnonvariable := by
  unfold CanonicalClassCoherent
  intro source
  let NodeCoherent : DependencyNode bindings → Prop := fun node =>
    ∀ assignment : ClassAssignment bindings node.1,
      canonicalNodeValue bindings hloopFree hnonvariable node =
        applyClassSolution
          (canonicalValuation bindings hloopFree hnonvariable)
          (toLeaTTaAtom assignment.1.2)
  change NodeCoherent source
  apply (dependencyOrder_wellFounded hloopFree).induction source
  intro source hsmaller assignment
  cases hchosen : chosenClassAssignment bindings source.1 with
  | none =>
      have hnonempty : Nonempty (ClassAssignment bindings source.1) :=
        ⟨assignment⟩
      simp [chosenClassAssignment, hnonempty] at hchosen
  | some chosen =>
      obtain ⟨pivot, hpivotChosen, hpivotAssignment⟩ :=
        hreconciled source chosen assignment
      have hpivotChosenEq := hpivotChosen.canonical_eq
        hloopFree hnonvariable hsmaller
      have hpivotAssignmentEq := hpivotAssignment.canonical_eq
        hloopFree hnonvariable hsmaller
      calc
        canonicalNodeValue bindings hloopFree hnonvariable source =
            applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom chosen.1.2) :=
          canonicalNodeValue_eq_applyClassSolution_of_chosen
            hloopFree hnonvariable chosen hchosen
        _ = applyClassSolution
              (canonicalValuation bindings hloopFree hnonvariable)
              (toLeaTTaAtom assignment.1.2) :=
          hpivotChosenEq.symm.trans hpivotAssignmentEq

/-- A loop-free normalized record with strictly-below reconciliation paths has
a concrete model. -/
theorem has_model_of_pathReconciled
    {bindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree bindings)
    (hnonvariable : AssignmentsNonVariable bindings)
    (hreconciled : ClassAssignmentsPathReconciled bindings) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation bindings := by
  refine ⟨canonicalValuation bindings hloopFree hnonvariable, ?_⟩
  exact canonicalValuation_satisfies_of_classCoherent
    hloopFree hnonvariable
    (canonicalClassCoherent_of_pathReconciled
      hloopFree hnonvariable hreconciled)

/-- Positive canary: a singleton assignment class has the reflexive path from
its only value to itself. -/
theorem structuralSolvedProbe_pathReconciled :
    ClassAssignmentsPathReconciled structuralSolvedProbe := by
  intro source left right
  rcases left with ⟨⟨leftKey, leftValue⟩, hleftMem, hleftClass⟩
  rcases right with ⟨⟨rightKey, rightValue⟩, hrightMem, hrightClass⟩
  have hleftPair : (leftKey, leftValue) = ("y", .symbol "a") := by
    simpa [structuralSolvedProbe, Bindings.assign,
      Bindings.isBound, Bindings.lookup, Bindings.empty] using hleftMem
  have hrightPair : (rightKey, rightValue) = ("y", .symbol "a") := by
    simpa [structuralSolvedProbe, Bindings.assign,
      Bindings.isBound, Bindings.lookup, Bindings.empty] using hrightMem
  cases hleftPair
  cases hrightPair
  have hbelow : AtomDependenciesBelow structuralSolvedProbe source
      (.symbol "a") := by
    intro name hoccurs
    cases hoccurs
  let pivot : ClassAssignment structuralSolvedProbe source.1 :=
    ⟨("y", .symbol "a"), hleftMem, hleftClass⟩
  exact ⟨pivot, .refl hbelow, .refl hbelow⟩

/-- Negative canary: an acyclic but incompatible class cannot acquire guarded
reconciliation paths through its own variables. -/
theorem incompatibleAcyclicProbe_not_pathReconciled :
    ¬ClassAssignmentsPathReconciled incompatibleAcyclicProbe := by
  intro hreconciled
  apply incompatibleAcyclicProbe_has_no_model
  exact has_model_of_pathReconciled
    incompatibleAcyclicProbe_loopFree
    incompatibleAcyclicProbe_nonvariable hreconciled

/-! ## Derivation-level reduction -/

/-- A constraint fold retains its entire live seed literally. -/
theorem mergeConstraintsRel_seed_subrecord
    {seed : Bindings} {constraints : List HumanMatchMergeSpec.Constraint}
    {out : Bindings}
    (hfold : HumanMatchMergeSpec.MergeConstraintsRel
      HumanMatchMergeSpec.equalityGroundedSemantic seed constraints out) :
    BindingSubrecord seed out := by
  apply HumanMatchMergeSpec.MergeConstraintsRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ seed out _ => BindingSubrecord seed out)
    (motive_3 := fun bindings _ _ out _ => BindingSubrecord bindings out)
    (motive_4 := fun bindings _ _ out _ => BindingSubrecord bindings out)
    (motive_5 := fun seed _ out _ => BindingSubrecord seed out)
    (motive_6 := fun left _ out _ => BindingSubrecord left out)
    (t := hfold)
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
        (isBound_false_of_classValues_nil hvalues)
  next =>
      intros
      exact BindingSubrecord.refl _
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

/-- Every equality class presented by the right binding record embeds into a
declarative merge result.  Equality insertion retains the requested edge even
when class values trigger recursive reconciliation; fold order is eliminated
by the relation's permutation witness. -/
theorem mergeRel_right_mem_eqClass
    {left right out : Bindings}
    (hmerge : HumanMatchMergeSpec.MergeRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right out) :
    ∀ {start finish},
      finish ∈ right.eqClass start → finish ∈ out.eqClass start := by
  intro start finish hclass
  apply HumanMatchMergeSpec.MergeRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun seed addedLeft addedRight result _ =>
      addedRight ∈ result.eqClass addedLeft)
    (motive_5 := fun _ constraints result _ =>
      ∀ addedLeft addedRight,
        HumanMatchMergeSpec.Constraint.equality addedLeft addedRight ∈
          constraints →
        addedRight ∈ result.eqClass addedLeft)
    (motive_6 := fun _ right result _ =>
      finish ∈ right.eqClass start → finish ∈ result.eqClass start)
    (t := hmerge)
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
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next =>
      intro seed addedLeft addedRight values hvalues hagree
      exact addEquality_right_mem_eqClass seed addedLeft addedRight
  next =>
      intro seed addedLeft addedRight first rest matched result hvalues
        hnotAgree hlist hmerge ihList ihMerge
      exact (mergeRel_left_subrecord hmerge).mem_eqClass
        (addEquality_right_mem_eqClass seed addedLeft addedRight)
  next =>
      intro seed addedLeft addedRight hmem
      simp at hmem
  next =>
      intro seed next result key value rest hadd htail ihAdd ihTail
        addedLeft addedRight hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · contradiction
      · exact ihTail addedLeft addedRight hmem
  next =>
      intro seed next result addedLeft addedRight rest hadd htail
        ihAdd ihTail queryLeft queryRight hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hmem
      · cases hhead
        exact (mergeConstraintsRel_seed_subrecord htail).mem_eqClass ihAdd
      · exact ihTail queryLeft queryRight hmem
  next =>
      intro left right result order horder hfold ihFold hrightClass
      apply eqClass_mono_of_equalities_solved
        (source := right) (target := result) (fun edgeLeft edgeRight hmem => ?_)
        hrightClass
      apply ihFold edgeLeft edgeRight
      exact (List.Perm.mem_iff horder).mpr
        (HumanMatchSolutionTheory.equality_mem_constraints_iff.mpr hmem)
  exact hclass

/-- Every visible value in the class joined by an equality-reconciliation
step is strictly below that class in every non-variable literal extension.
This supplies the endpoint guards for the remaining local path theorem. -/
theorem addEquality_classValue_dependenciesBelow
    {target bindings : Bindings} {left right : String}
    {first : Atom} {rest : List Atom}
    (hnodup : AssignmentsNodup bindings)
    (hvalues : (first :: rest).Perm
      ((bindings.addEquality left right).classValues left))
    (hsubrecord : BindingSubrecord
      (bindings.addEquality left right) target)
    (hnonvariable : AssignmentsNonVariable target)
    (source : DependencyNode target)
    (hsource : source.1 ∈ target.eqClass left)
    {value : Atom} (hvalue : value ∈ first :: rest) :
    AtomDependenciesBelow target source value := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  have hvisible : value ∈ candidate.classValues left :=
    (List.Perm.mem_iff hvalues).mp hvalue
  obtain ⟨key, hassignment, hkeyClass⟩ :=
    exists_assignment_of_mem_classValues hvisible
  have htargetAssignment : (key, value) ∈ target.assignments :=
    hsubrecord.1 _ (by simpa [candidate] using hassignment)
  have htargetKeyClass : key ∈ target.eqClass left :=
    hsubrecord.mem_eqClass (by simpa [candidate] using hkeyClass)
  have hkeySource : key ∈ target.eqClass source.1 := by
    rw [EqualityClosure.mem_eqClass_iff_reachable]
      at hsource htargetKeyClass ⊢
    exact hsource.symm.trans htargetKeyClass
  let assignment : ClassAssignment target source.1 :=
    ⟨(key, value), htargetAssignment, hkeySource⟩
  exact ClassAssignment.value_dependenciesBelow_source
    hnonvariable assignment

/-! ## Canonical satisfaction below one dependency frontier -/

/-- Once a literal assignment's key class lies strictly below the ambient
class, the dependency induction hypothesis makes that assignment true in the
canonical valuation. -/
theorem canonical_assignment_eq_of_key_below
    {target : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree target)
    (hnonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (hsmaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target hloopFree hnonvariable node =
          applyClassSolution
            (canonicalValuation target hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {key : String} {value : Atom}
    (hassignment : (key, value) ∈ target.assignments)
    (hkeyBelow : AtomDependenciesBelow target source (.var key)) :
    canonicalValuation target hloopFree hnonvariable key =
      applyClassSolution
        (canonicalValuation target hloopFree hnonvariable)
        (toLeaTTaAtom value) := by
  obtain ⟨hkeySupport, hlt⟩ := hkeyBelow key (.var key)
  let node : DependencyNode target :=
    representativeNode ⟨key, hkeySupport⟩
  have hkeyClass : key ∈ target.eqClass node.1 := by
    exact mem_eqClass_symm
      (eqRepresentative_mem_eqClass target key)
  let assignment : ClassAssignment target node.1 :=
    ⟨(key, value), hassignment, hkeyClass⟩
  have hcoherent := hsmaller node hlt assignment
  simpa [node, canonicalValuation, hkeySupport] using hcoherent

/-- A visible class value in a literal subrecord is canonically equal to every
variable naming that class, provided the class lies below the ambient
dependency frontier. -/
theorem canonical_eq_classValue_of_subrecord_below
    {target sourceBindings : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree target)
    (hnonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (hsmaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target hloopFree hnonvariable node =
          applyClassSolution
            (canonicalValuation target hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    (hsubrecord : BindingSubrecord sourceBindings target)
    {key : String} {value : Atom}
    (hkeyBelow : AtomDependenciesBelow target source (.var key))
    (hvalue : value ∈ sourceBindings.classValues key) :
    canonicalValuation target hloopFree hnonvariable key =
      applyClassSolution
        (canonicalValuation target hloopFree hnonvariable)
        (toLeaTTaAtom value) := by
  obtain ⟨storedKey, hassignment, hstoredClass⟩ :=
    exists_assignment_of_mem_classValues hvalue
  have htargetAssignment : (storedKey, value) ∈ target.assignments :=
    hsubrecord.1 _ hassignment
  have htargetClass : storedKey ∈ target.eqClass key :=
    hsubrecord.mem_eqClass hstoredClass
  have hstoredBelow := hkeyBelow.var_of_mem_eqClass htargetClass
  have hstoredEq := canonical_assignment_eq_of_key_below
    hloopFree hnonvariable hsmaller htargetAssignment hstoredBelow
  obtain ⟨hkeySupport, _hlt⟩ := hkeyBelow key (.var key)
  exact (canonicalValuation_eq_of_mem_eqClass
      hloopFree hnonvariable hkeySupport htargetClass).trans hstoredEq

/-- A value visible in a literal subrecord's class lies below every ambient
class below which that class's variable lies. -/
theorem classValue_dependenciesBelow_of_subrecord
    {target sourceBindings : Bindings}
    (hnonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (hsubrecord : BindingSubrecord sourceBindings target)
    {key : String} {value : Atom}
    (hkeyBelow : AtomDependenciesBelow target source (.var key))
    (hvalue : value ∈ sourceBindings.classValues key) :
    AtomDependenciesBelow target source value := by
  obtain ⟨storedKey, hassignment, hstoredClass⟩ :=
    exists_assignment_of_mem_classValues hvalue
  have htargetAssignment : (storedKey, value) ∈ target.assignments :=
    hsubrecord.1 _ hassignment
  have htargetClass : storedKey ∈ target.eqClass key :=
    hsubrecord.mem_eqClass hstoredClass
  let assignment : ClassAssignment target key :=
    ⟨(storedKey, value), htargetAssignment, htargetClass⟩
  exact ClassAssignment.value_dependenciesBelow_of_atomOccurs
    hnonvariable hkeyBelow (.var key) assignment

/-- The final equation in a replicated-pivot reconciliation list is the pivot
equation for the newly proposed value. -/
private theorem map_replicate_append_singleton_last
    {α β : Type} (mapAtom : α → β)
    (pivot value : α) (rest : List α)
    (heq : (List.replicate (rest.length + 1) pivot).map mapAtom =
      (rest ++ [value]).map mapAtom) :
    mapAtom pivot = mapAtom value := by
  induction rest with
  | nil => simpa using heq
  | cons head rest ih =>
      simp only [List.length_cons, Nat.add_assoc,
        List.replicate_succ, List.map_cons, List.cons.injEq,
        List.cons_append] at heq
      exact ih heq.2

/-- Every element on the right of a replicated-pivot list equation evaluates
to the pivot. -/
private theorem map_replicate_eq_each
    {α β : Type} (mapAtom : α → β) (pivot : α) :
    ∀ (rest : List α),
      (List.replicate rest.length pivot).map mapAtom = rest.map mapAtom →
      ∀ value ∈ pivot :: rest, mapAtom pivot = mapAtom value
  | [], heq, value, hmem => by
      simp only [List.mem_singleton] at hmem
      subst value
      rfl
  | head :: rest, heq, value, hmem => by
      simp only [List.length_cons, List.replicate_succ, List.map_cons,
        List.cons.injEq] at heq
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rfl
      · rcases hmem with rfl | hmem
        · exact heq.1
        · exact map_replicate_eq_each mapAtom pivot rest heq.2 value
            (by simp [hmem])

/-- Simultaneous strict-scope and semantic replay for a human merge.  Its
second projection is the crucial asymmetrical fact: below one ambient class,
the canonical valuation satisfies the *right* binding record even if merge-
back consumed that record's concrete assignments.  The live left accumulator
need not yet be satisfied. -/
private theorem mergeRel_below_pack
    {target : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree target)
    (hnonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (hsmaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target hloopFree hnonvariable node =
          applyClassSolution
            (canonicalValuation target hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right out : Bindings}
    (hmerge : HumanMatchMergeSpec.MergeRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right out) :
    (BindingDependenciesBelow target source left →
      BindingDependenciesBelow target source right →
        BindingDependenciesBelow target source out) ∧
    (BindingSubrecord out target →
      BindingDependenciesBelow target source right →
        HEBindingSatisfied
          (canonicalValuation target hloopFree hnonvariable) right) := by
  let valuation := canonicalValuation target hloopFree hnonvariable
  apply HumanMatchMergeSpec.MergeRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun left right seed result _ =>
      BindingDependenciesBelow target source seed →
      AtomsDependenciesBelow target source left →
      AtomsDependenciesBelow target source right →
        BindingDependenciesBelow target source result)
    (motive_3 := fun seed key value result _ =>
      (BindingDependenciesBelow target source seed →
        AtomDependenciesBelow target source (.var key) →
        AtomDependenciesBelow target source value →
          BindingDependenciesBelow target source result) ∧
      (BindingSubrecord result target →
        AtomDependenciesBelow target source (.var key) →
        AtomDependenciesBelow target source value →
          valuation key =
            applyClassSolution valuation (toLeaTTaAtom value)))
    (motive_4 := fun seed addedLeft addedRight result _ =>
      (BindingDependenciesBelow target source seed →
        AtomDependenciesBelow target source (.var addedLeft) →
        AtomDependenciesBelow target source (.var addedRight) →
          BindingDependenciesBelow target source result) ∧
      (BindingSubrecord result target →
        AtomDependenciesBelow target source (.var addedLeft) →
        AtomDependenciesBelow target source (.var addedRight) →
          valuation addedLeft = valuation addedRight))
    (motive_5 := fun seed constraints result _ =>
      (BindingDependenciesBelow target source seed →
        ConstraintsDependenciesBelow target source constraints →
          BindingDependenciesBelow target source result) ∧
      (BindingSubrecord result target →
        ConstraintsDependenciesBelow target source constraints →
          HumanMatchSolutionTheory.ConstraintsSatisfied valuation
            constraints))
    (motive_6 := fun left right result _ =>
      (BindingDependenciesBelow target source left →
        BindingDependenciesBelow target source right →
          BindingDependenciesBelow target source result) ∧
      (BindingSubrecord result target →
        BindingDependenciesBelow target source right →
          HEBindingSatisfied valuation right))
    (t := hmerge)
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next =>
      intro seed hseed hleft hright
      exact hseed
  next =>
      intro headLeft headRight tailLeft tailRight seed matched next result
        hhead hheadMerge htail ihHead ihMerge ihTail
        hseed hlefts hrights
      have hleft : AtomDependenciesBelow target source headLeft :=
        hlefts headLeft (by simp)
      have hright : AtomDependenciesBelow target source headRight :=
        hrights headRight (by simp)
      have hmatched := humanMatch_dependenciesBelow hhead hleft hright
      have hnext := ihMerge.1 hseed hmatched
      apply ihTail hnext
      · intro atom hmem
        exact hlefts atom (by simp [hmem])
      · intro atom hmem
        exact hrights atom (by simp [hmem])
  next =>
      intro seed key value hvalues
      constructor
      · intro hseed hkey hvalue
        exact hseed.assign hkey hvalue
      · intro hout hkey hvalue
        have hbound := isBound_false_of_classValues_nil hvalues
        have hassignment :
            (key, value) ∈ (seed.assign key value).assignments := by
          simp [Bindings.assign, hbound]
        exact canonical_assignment_eq_of_key_below
          hloopFree hnonvariable hsmaller
          (hout.1 _ hassignment) hkey
  next =>
      intro seed key value first rest hvalues hagree hvalueEq
      constructor
      · intro hseed hkey hvalue
        exact hseed
      · intro hout hkey hvalue
        subst value
        apply canonical_eq_classValue_of_subrecord_below
          hloopFree hnonvariable hsmaller hout hkey
        exact (List.Perm.mem_iff hvalues).mp (by simp)
  next =>
      intro seed key value first rest matched result hvalues hagree hne
        hhead hheadMerge ihHead ihMerge
      constructor
      · intro hseed hkey hvalue
        have hfirst : AtomDependenciesBelow target source first := by
          apply hseed.value_of_mem_classValues
          exact (List.Perm.mem_iff hvalues).mp (by simp)
        exact ihMerge.1 hseed
          (humanMatch_dependenciesBelow hhead hfirst hvalue)
      · intro hout hkey hvalue
        have hfirstMem : first ∈ seed.classValues key :=
          (List.Perm.mem_iff hvalues).mp (by simp)
        have hseedTarget :=
          (mergeRel_left_subrecord hheadMerge).trans hout
        have hfirst : AtomDependenciesBelow target source first :=
          classValue_dependenciesBelow_of_subrecord
            hnonvariable hseedTarget hkey hfirstMem
        have hmatched := humanMatch_dependenciesBelow hhead hfirst hvalue
        have hmatchedSatisfied := ihMerge.2 hout hmatched
        have hfirstValue :=
          (HumanMatchSolutionTheory.matchRel_solution_iff
            hhead valuation).mp hmatchedSatisfied
        exact (canonical_eq_classValue_of_subrecord_below
          hloopFree hnonvariable hsmaller hseedTarget hkey
          hfirstMem).trans hfirstValue
  next =>
      intro seed key value first rest matched result hvalues hnotAgree
        hlist hheadMerge ihList ihMerge
      constructor
      · intro hseed hkey hvalue
        have hall : ∀ candidate ∈ first :: rest,
            AtomDependenciesBelow target source candidate := by
          intro candidate hmem
          apply hseed.value_of_mem_classValues
          exact (List.Perm.mem_iff hvalues).mp hmem
        have hmatched := ihList
          (BindingDependenciesBelow.empty target source)
          (by
            intro candidate hmem
            rcases List.mem_replicate.mp hmem with ⟨_, hcandidate⟩
            subst candidate
            exact hall first (by simp))
          (by
            intro candidate hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hrest | rfl
            · exact hall candidate (by simp [hrest])
            · exact hvalue)
        exact ihMerge.1 hseed hmatched
      · intro hout hkey hvalue
        have hfirstMem : first ∈ seed.classValues key :=
          (List.Perm.mem_iff hvalues).mp (by simp)
        have hseedTarget :=
          (mergeRel_left_subrecord hheadMerge).trans hout
        have hall : ∀ candidate ∈ first :: rest,
            AtomDependenciesBelow target source candidate := by
          intro candidate hmem
          apply classValue_dependenciesBelow_of_subrecord
            hnonvariable hseedTarget hkey
          exact (List.Perm.mem_iff hvalues).mp hmem
        have hmatched := ihList
          (BindingDependenciesBelow.empty target source)
          (by
            intro candidate hmem
            rcases List.mem_replicate.mp hmem with ⟨_, hcandidate⟩
            subst candidate
            exact hall first (by simp))
          (by
            intro candidate hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hrest | rfl
            · exact hall candidate (by simp [hrest])
            · exact hvalue)
        have hmatchedSatisfied := ihMerge.2 hout hmatched
        have hitems :=
          (HumanMatchSolutionTheory.matchListAccRel_solution_iff
            hlist valuation).mp hmatchedSatisfied |>.2
        have hfirstValue :
            applyClassSolution valuation (toLeaTTaAtom first) =
              applyClassSolution valuation (toLeaTTaAtom value) := by
          apply map_replicate_append_singleton_last
            (fun atom =>
              applyClassSolution valuation (toLeaTTaAtom atom))
            first value rest
          simpa [solutionTheory_toLeaTTaAtoms_eq_map,
            List.map_map, Function.comp_def] using hitems
        exact (canonical_eq_classValue_of_subrecord_below
          hloopFree hnonvariable hsmaller hseedTarget hkey
          hfirstMem).trans hfirstValue
  next =>
      intro seed addedLeft addedRight values hvalues hagree
      constructor
      · intro hseed hleft hright
        exact hseed.addEquality hleft hright
      · intro hout hleft hright
        apply canonicalValuation_satisfies_equalities
          hloopFree hnonvariable addedLeft addedRight
        apply hout.2
        simp [Bindings.addEquality]
  next =>
      intro seed addedLeft addedRight first rest matched result hvalues
        hnotAgree hlist hheadMerge ihList ihMerge
      constructor
      · intro hseed hleft hright
        have hcandidate := hseed.addEquality hleft hright
        have hall : ∀ candidate ∈ first :: rest,
            AtomDependenciesBelow target source candidate := by
          intro candidate hmem
          apply hcandidate.value_of_mem_classValues
          exact (List.Perm.mem_iff hvalues).mp hmem
        have hmatched := ihList
          (BindingDependenciesBelow.empty target source)
          (by
            intro candidate hmem
            rcases List.mem_replicate.mp hmem with ⟨_, hcandidateEq⟩
            subst candidate
            exact hall first (by simp))
          (by
            intro candidate hmem
            exact hall candidate (by simp [hmem]))
        exact ihMerge.1 hcandidate hmatched
      · intro hout hleft hright
        have hcandidateTarget :=
          (mergeRel_left_subrecord hheadMerge).trans hout
        apply canonicalValuation_satisfies_equalities
          hloopFree hnonvariable addedLeft addedRight
        apply hcandidateTarget.2
        simp [Bindings.addEquality]
  next =>
      intro seed
      constructor
      · intro hseed hconstraints
        exact hseed
      · intro hout hconstraints constraint hmem
        simp at hmem
  next =>
      intro seed next result key value rest hadd htail ihAdd ihTail
      constructor
      · intro hseed hconstraints
        have hhead := hconstraints (.value key value) (by simp)
        apply ihTail.1 (ihAdd.1 hseed hhead.1 hhead.2)
        intro constraint hmem
        exact hconstraints constraint (by simp [hmem])
      · intro hout hconstraints constraint hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · have hhead := hconstraints (.value key value) (by simp)
          exact ihAdd.2
            ((mergeConstraintsRel_seed_subrecord htail).trans hout)
            hhead.1 hhead.2
        · exact ihTail.2 hout
            (fun candidate hcandidate =>
              hconstraints candidate (by simp [hcandidate]))
            constraint hmem
  next =>
      intro seed next result addedLeft addedRight rest hadd htail
        ihAdd ihTail
      constructor
      · intro hseed hconstraints
        have hhead := hconstraints (.equality addedLeft addedRight) (by simp)
        apply ihTail.1 (ihAdd.1 hseed hhead.1 hhead.2)
        intro constraint hmem
        exact hconstraints constraint (by simp [hmem])
      · intro hout hconstraints constraint hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · have hhead :=
            hconstraints (.equality addedLeft addedRight) (by simp)
          exact ihAdd.2
            ((mergeConstraintsRel_seed_subrecord htail).trans hout)
            hhead.1 hhead.2
        · exact ihTail.2 hout
            (fun candidate hcandidate =>
              hconstraints candidate (by simp [hcandidate]))
            constraint hmem
  next =>
      intro mergedLeft mergedRight result order horder hfold ihFold
      constructor
      · intro hleft hright
        apply ihFold.1 hleft
        intro constraint hmem
        have hrightMem : constraint ∈
            HumanMatchMergeSpec.constraints mergedRight :=
          (List.Perm.mem_iff horder).mp hmem
        cases constraint with
        | value key value =>
            exact hright.assignments key value
              (HumanMatchSolutionTheory.value_mem_constraints_iff.mp
                hrightMem)
        | equality edgeLeft edgeRight =>
            exact hright.equalities edgeLeft edgeRight
              (HumanMatchSolutionTheory.equality_mem_constraints_iff.mp
                hrightMem)
      · intro hout hright
        have hconstraints : ConstraintsDependenciesBelow target source order := by
          intro constraint hmem
          have hrightMem : constraint ∈
              HumanMatchMergeSpec.constraints mergedRight :=
            (List.Perm.mem_iff horder).mp hmem
          cases constraint with
          | value key value =>
              exact hright.assignments key value
                (HumanMatchSolutionTheory.value_mem_constraints_iff.mp
                  hrightMem)
          | equality edgeLeft edgeRight =>
              exact hright.equalities edgeLeft edgeRight
                (HumanMatchSolutionTheory.equality_mem_constraints_iff.mp
                  hrightMem)
        have horderSatisfied := ihFold.2 hout hconstraints
        apply (HumanMatchSolutionTheory.constraintsSatisfied_constraints_iff
          valuation mergedRight).mp
        exact (HumanMatchSolutionTheory.constraintsSatisfied_iff_of_perm
          horder).mp horderSatisfied

/-- Public projection of `mergeRel_below_pack`: a successful merge semantically
replays every scoped right-hand constraint below the ambient class, without
assuming that the live left accumulator is already coherent. -/
theorem mergeRel_right_satisfied_of_dependenciesBelow
    {target : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree target)
    (hnonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (hsmaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target hloopFree hnonvariable node =
          applyClassSolution
            (canonicalValuation target hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right out : Bindings}
    (hmerge : HumanMatchMergeSpec.MergeRel
      HumanMatchMergeSpec.equalityGroundedSemantic left right out)
    (hout : BindingSubrecord out target)
    (hright : BindingDependenciesBelow target source right) :
    HEBindingSatisfied
      (canonicalValuation target hloopFree hnonvariable) right :=
  (mergeRel_below_pack hloopFree hnonvariable hsmaller hmerge).2
    hout hright

/-- List projection of the same dependency-scope invariant.  Each child match
supplies the scope of its transient result, and the merge pack transports that
scope through the live accumulator before the tail continues. -/
theorem matchListAccRel_dependenciesBelow
    {target : Bindings}
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree target)
    (hnonvariable : AssignmentsNonVariable target)
    {source : DependencyNode target}
    (hsmaller : ∀ node : DependencyNode target,
      DependencyOrder target node source →
      ∀ assignment : ClassAssignment target node.1,
        canonicalNodeValue target hloopFree hnonvariable node =
          applyClassSolution
            (canonicalValuation target hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2))
    {left right : List Atom} {seed result : Bindings}
    (hlist : HumanMatchMergeSpec.MatchListAccRel
      HumanMatchMergeSpec.equalityGroundedSemantic
      left right seed result)
    (hleft : AtomsDependenciesBelow target source left)
    (hright : AtomsDependenciesBelow target source right)
    (hseed : BindingDependenciesBelow target source seed) :
    BindingDependenciesBelow target source result := by
  refine (HumanMatchMergeSpec.MatchListAccRel.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun left right seed result _ =>
      AtomsDependenciesBelow target source left →
      AtomsDependenciesBelow target source right →
      BindingDependenciesBelow target source seed →
        BindingDependenciesBelow target source result)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (t := hlist)) hleft hright hseed
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next => intros; trivial
  next =>
      intro live hleft hright hseed
      exact hseed
  next =>
      intro headLeft headRight tailLeft tailRight live matched next result
        hhead hmerge htail ihHead ihMerge ihTail hlefts hrights hlive
      have hheadLeft := hlefts headLeft (by simp)
      have hheadRight := hrights headRight (by simp)
      have hmatched :=
        humanMatch_dependenciesBelow hhead hheadLeft hheadRight
      have hnext :=
        (mergeRel_below_pack hloopFree hnonvariable hsmaller hmerge).1
          hlive hmatched
      apply ihTail
      · intro atom hmem
        exact hlefts atom (by simp [hmem])
      · intro atom hmem
        exact hrights atom (by simp [hmem])
      · exact hnext
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

/-! ## Fixed-target semantic class coherence -/

/-- Every pair of source assignments whose keys lie in one source equality
class evaluates equally in the eventual target valuation.  Literal source
inclusion is retained separately so later folds may continue to reason about
stored class values. -/
structure ClassAssignmentsEvalCoherentIn
    (target source : Bindings) (valuation : String → Metta.Atom)
    (ambient : DependencyNode target) : Prop where
  subrecord : BindingSubrecord source target
  values : ∀ {leftKey rightKey : String} {leftValue rightValue : Atom},
    (leftKey, leftValue) ∈ source.assignments →
    (rightKey, rightValue) ∈ source.assignments →
    rightKey ∈ source.eqClass leftKey →
    leftKey ∈ target.eqClass ambient.1 →
      applyClassSolution valuation (toLeaTTaAtom leftValue) =
        applyClassSolution valuation (toLeaTTaAtom rightValue)

/-- The empty live accumulator is semantically coherent in every target. -/
theorem evalCoherentIn_empty
    (target : Bindings) (valuation : String → Metta.Atom)
    (ambient : DependencyNode target) :
    ClassAssignmentsEvalCoherentIn target Bindings.empty valuation ambient where
  subrecord := by
    constructor <;> intro relation hmem <;> simp [Bindings.empty] at hmem
  values hleft := by simp [Bindings.empty] at hleft

/-- Semantic class coherence restricts to every literal source subrecord. -/
theorem ClassAssignmentsEvalCoherentIn.of_source_subrecord
    {target source before : Bindings} {valuation : String → Metta.Atom}
    {ambient : DependencyNode target}
    (hcoherent : ClassAssignmentsEvalCoherentIn
      target source valuation ambient)
    (hbefore : BindingSubrecord before source) :
    ClassAssignmentsEvalCoherentIn target before valuation ambient where
  subrecord := hbefore.trans hcoherent.subrecord
  values hleft hright hclass hambient :=
    hcoherent.values
      (hbefore.1 _ hleft) (hbefore.1 _ hright)
      (hbefore.mem_eqClass hclass) hambient

/-- Adding the first assignment in a class preserves fixed-target semantic
coherence. -/
theorem evalCoherentIn_assign_of_classValues_nil
    {target bindings : Bindings} {valuation : String → Metta.Atom}
    {ambient : DependencyNode target}
    {key : String} {value : Atom}
    (hcoherent : ClassAssignmentsEvalCoherentIn
      target bindings valuation ambient)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : bindings.classValues key = [])
    (hout : BindingSubrecord (bindings.assign key value) target) :
    ClassAssignmentsEvalCoherentIn
      target (bindings.assign key value) valuation ambient := by
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass hambient
  have hbound := isBound_false_of_classValues_nil hvalues
  have hleftCases :
      (leftKey, leftValue) ∈ bindings.assignments ∨
        (leftKey = key ∧ leftValue = value) := by
    simpa [Bindings.assign, hbound] using hleft
  have hrightCases :
      (rightKey, rightValue) ∈ bindings.assignments ∨
        (rightKey = key ∧ rightValue = value) := by
    simpa [Bindings.assign, hbound] using hright
  have hclassOld : rightKey ∈ bindings.eqClass leftKey := by
    simpa [Bindings.eqClass, Bindings.assign, hbound] using hclass
  rcases hleftCases with hleftOld | ⟨hleftKey, hleftValue⟩
  · rcases hrightCases with hrightOld | ⟨hrightKey, hrightValue⟩
    · exact hcoherent.values hleftOld hrightOld hclassOld hambient
    · have hleftClass : leftKey ∈ bindings.eqClass key := by
        rw [hrightKey] at hclassOld
        exact mem_eqClass_symm hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hleftOld hleftClass
      rw [hvalues] at hvisible
      simp at hvisible
  · rcases hrightCases with hrightOld | ⟨hrightKey, hrightValue⟩
    · have hrightClass : rightKey ∈ bindings.eqClass key := by
        simpa [hleftKey] using hclassOld
      have hvisible := assignment_value_mem_classValues
        hnodup hrightOld hrightClass
      rw [hvalues] at hvisible
      simp at hvisible
    · simp [hleftValue, hrightValue]

/-- Literal agreement of all values in a newly joined class preserves
fixed-target semantic coherence. -/
theorem evalCoherentIn_addEquality_of_valuesAgree
    {target bindings : Bindings} {valuation : String → Metta.Atom}
    {ambient : DependencyNode target}
    {left right : String}
    (hcoherent : ClassAssignmentsEvalCoherentIn
      target bindings valuation ambient)
    (hnodup : AssignmentsNodup bindings)
    (hagree : HumanMatchMergeSpec.ValuesAgree
      ((bindings.addEquality left right).classValues left))
    (hout : BindingSubrecord (bindings.addEquality left right) target) :
    ClassAssignmentsEvalCoherentIn
      target (bindings.addEquality left right) valuation ambient := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass hambient
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hvalueEq := valuesAgree_eq_of_mem
      hagree hleftVisible hrightVisible
    subst rightValue
    rfl
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    exact hcoherent.values hleftOld hrightOld hclassOld hambient

/-- A recursively established pivot equation to every value in the newly
joined class preserves fixed-target semantic coherence. -/
theorem evalCoherentIn_addEquality_of_pivot
    {target bindings : Bindings} {valuation : String → Metta.Atom}
    {ambient : DependencyNode target}
    {left right : String} {first : Atom} {rest : List Atom}
    (hcoherent : ClassAssignmentsEvalCoherentIn
      target bindings valuation ambient)
    (hnodup : AssignmentsNodup bindings)
    (hvalues : (first :: rest).Perm
      ((bindings.addEquality left right).classValues left))
    (hout : BindingSubrecord (bindings.addEquality left right) target)
    (hpivot : ∀ value ∈ first :: rest,
      applyClassSolution valuation (toLeaTTaAtom first) =
        applyClassSolution valuation (toLeaTTaAtom value)) :
    ClassAssignmentsEvalCoherentIn
      target (bindings.addEquality left right) valuation ambient := by
  let candidate := bindings.addEquality left right
  have hcandidateNodup : AssignmentsNodup candidate := by
    simpa [candidate, AssignmentsNodup, Bindings.addEquality] using hnodup
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass hambient
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  by_cases hjoined : leftKey ∈ candidate.eqClass left
  · have hrightJoined : rightKey ∈ candidate.eqClass left := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hjoined hclass ⊢
      exact hjoined.trans hclass
    have hleftVisible : leftValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hleft hjoined
    have hrightVisible : rightValue ∈ candidate.classValues left :=
      assignment_value_mem_classValues
        hcandidateNodup hright hrightJoined
    have hleftList : leftValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hleftVisible
    have hrightList : rightValue ∈ first :: rest :=
      (List.Perm.mem_iff hvalues).mpr hrightVisible
    exact (hpivot leftValue hleftList).symm.trans
      (hpivot rightValue hrightList)
  · have houtside : left ∉ candidate.eqClass leftKey := by
      intro hleft
      exact hjoined (mem_eqClass_symm hleft)
    have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
      mem_eqClass_old_of_not_mem_addEquality
        bindings left right (by simpa [candidate] using houtside)
          (by simpa [candidate] using hclass)
    exact hcoherent.values hleftOld hrightOld hclassOld hambient

/-- Adding an equality edge outside the fixed ambient class cannot change
semantic coherence inside that class. -/
theorem evalCoherentIn_addEquality_of_ambient_outside
    {target bindings : Bindings} {valuation : String → Metta.Atom}
    {ambient : DependencyNode target}
    {left right : String}
    (hcoherent : ClassAssignmentsEvalCoherentIn
      target bindings valuation ambient)
    (hout : BindingSubrecord (bindings.addEquality left right) target)
    (houtside : ambient.1 ∉ target.eqClass left) :
    ClassAssignmentsEvalCoherentIn
      target (bindings.addEquality left right) valuation ambient := by
  let candidate := bindings.addEquality left right
  refine ⟨hout, ?_⟩
  intro leftKey rightKey leftValue rightValue hleft hright hclass hambient
  have hleftOld : (leftKey, leftValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hleft
  have hrightOld : (rightKey, rightValue) ∈ bindings.assignments := by
    simpa [candidate, Bindings.addEquality] using hright
  have hnotJoined : left ∉ candidate.eqClass leftKey := by
    intro hleftJoined
    have htargetJoined : left ∈ target.eqClass leftKey :=
      hout.mem_eqClass (by simpa [candidate] using hleftJoined)
    have hleftInAmbient : left ∈ target.eqClass ambient.1 := by
      rw [EqualityClosure.mem_eqClass_iff_reachable]
        at hambient htargetJoined ⊢
      exact hambient.trans htargetJoined
    exact houtside (mem_eqClass_symm hleftInAmbient)
  have hclassOld : rightKey ∈ bindings.eqClass leftKey :=
    mem_eqClass_old_of_not_mem_addEquality
      bindings left right (by simpa [candidate] using hnotJoined)
        (by simpa [candidate] using hclass)
  exact hcoherent.values hleftOld hrightOld hclassOld hambient

/-- At one dependency frontier, every live accumulator produced by a human
match derivation has pairwise-equal class values in the final canonical
valuation.  The equality-reconciliation branch is the only semantic branch:
it replays the scoped transient list match through `mergeRel_below_pack` and
then uses the list solution theorem to establish the pivot equations. -/
private theorem humanMatch_evalCoherentAt
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree out)
    (hnonvariable : AssignmentsNonVariable out)
    (source : DependencyNode out)
    (hsmaller : ∀ node : DependencyNode out,
      DependencyOrder out node source →
      ∀ assignment : ClassAssignment out node.1,
        canonicalNodeValue out hloopFree hnonvariable node =
          applyClassSolution
            (canonicalValuation out hloopFree hnonvariable)
            (toLeaTTaAtom assignment.1.2)) :
    ClassAssignmentsEvalCoherentIn out out
      (canonicalValuation out hloopFree hnonvariable) source := by
  let valuation := canonicalValuation out hloopFree hnonvariable
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun _ _ result _ =>
      BindingSubrecord result out →
      AssignmentsNodup result →
        ClassAssignmentsEvalCoherentIn out result valuation source)
    (motive_2 := fun _ _ seed result _ =>
      BindingSubrecord result out →
      AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn out seed valuation source →
        ClassAssignmentsEvalCoherentIn out result valuation source ∧
          AssignmentsNodup result)
    (motive_3 := fun seed _ _ result _ =>
      BindingSubrecord result out →
      AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn out seed valuation source →
        ClassAssignmentsEvalCoherentIn out result valuation source ∧
          AssignmentsNodup result)
    (motive_4 := fun seed _ _ result _ =>
      BindingSubrecord result out →
      AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn out seed valuation source →
        ClassAssignmentsEvalCoherentIn out result valuation source ∧
          AssignmentsNodup result)
    (motive_5 := fun seed _ result _ =>
      BindingSubrecord result out →
      AssignmentsNodup seed →
      ClassAssignmentsEvalCoherentIn out seed valuation source →
        ClassAssignmentsEvalCoherentIn out result valuation source ∧
          AssignmentsNodup result)
    (motive_6 := fun left _ result _ =>
      BindingSubrecord result out →
      AssignmentsNodup left →
      ClassAssignmentsEvalCoherentIn out left valuation source →
        ClassAssignmentsEvalCoherentIn out result valuation source ∧
          AssignmentsNodup result)
    (t := hmatch)
  next =>
      intro symbol hadmissible hout hnodup
      exact evalCoherentIn_empty out valuation source
  next =>
      intro left right hadmissible hout hnodup
      apply evalCoherentIn_addEquality_of_valuesAgree
        (evalCoherentIn_empty out valuation source)
        (by simp [AssignmentsNodup, Bindings.empty])
        (by
          simp [HumanMatchMergeSpec.ValuesAgree, Bindings.classValues,
            Bindings.lookup, Bindings.empty, Bindings.addEquality]) hout
  next =>
      intro key value hnonvar hadmissible hout hnodup
      apply evalCoherentIn_assign_of_classValues_nil
        (evalCoherentIn_empty out valuation source)
        (by simp [AssignmentsNodup, Bindings.empty])
        (by
          simp [Bindings.classValues, Bindings.lookup, Bindings.empty]) hout
  next =>
      intro value key hnonvar hadmissible hout hnodup
      apply evalCoherentIn_assign_of_classValues_nil
        (evalCoherentIn_empty out valuation source)
        (by simp [AssignmentsNodup, Bindings.empty])
        (by
          simp [Bindings.classValues, Bindings.lookup, Bindings.empty]) hout
  next =>
      intro left right result hitems hadmissible ih hout hnodup
      exact (ih hout
        (by simp [AssignmentsNodup, Bindings.empty])
        (evalCoherentIn_empty out valuation source)).1
  next =>
      intro grounded right result hright hcustom hground hadmissible
        hout hnodup
      rcases hground with ⟨hrightEq, houtEq⟩
      subst right
      subst result
      exact evalCoherentIn_empty out valuation source
  next =>
      intro left grounded result hleft hleftNoCustom hcustom hground
        hadmissible hout hnodup
      rcases hground with ⟨hleftEq, houtEq⟩
      subst left
      subst result
      exact evalCoherentIn_empty out valuation source
  next =>
      intro left right hleft hright hadmissible
      exact (hleft (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim
  next =>
      intro seed hout hnodup hcoherent
      exact ⟨hcoherent, hnodup⟩
  next =>
      intro headLeft headRight tailLeft tailRight seed matched next result
        hhead hmerge htail ihHead ihMerge ihTail
        hout hseedNodup hcoherent
      have hnextOut := matchListAccRel_seed_subrecord htail
      obtain ⟨hnextCoherent, hnextNodup⟩ :=
        ihMerge (hnextOut.trans hout) hseedNodup hcoherent
      exact ihTail hout hnextNodup hnextCoherent
  next =>
      intro seed key value hvalues hout hseedNodup hcoherent
      exact ⟨evalCoherentIn_assign_of_classValues_nil
          hcoherent hseedNodup hvalues hout,
        assignmentsNodup_assign hseedNodup⟩
  next =>
      intro seed key value first rest hvalues hagree hvalue
        hout hseedNodup hcoherent
      exact ⟨hcoherent, hseedNodup⟩
  next =>
      intro seed key value first rest matched result hvalues hagree hne
        hhead hmerge ihHead ihMerge hout hseedNodup hcoherent
      exact ihMerge hout hseedNodup hcoherent
  next =>
      intro seed key value first rest matched result hvalues hnotAgree
        hlist hmerge ihList ihMerge hout hseedNodup hcoherent
      exact ihMerge hout hseedNodup hcoherent
  next =>
      intro seed addedLeft addedRight values hvalues hagree
        hout hseedNodup hcoherent
      have hagree' : HumanMatchMergeSpec.ValuesAgree
          ((seed.addEquality addedLeft addedRight).classValues addedLeft) := by
        rw [hvalues]
        exact hagree
      exact ⟨evalCoherentIn_addEquality_of_valuesAgree
          hcoherent hseedNodup hagree' hout,
        by simpa [AssignmentsNodup, Bindings.addEquality] using hseedNodup⟩
  next =>
      intro seed addedLeft addedRight first rest matched result hvalues
        hnotAgree hlist hmerge ihList ihMerge
        hout hseedNodup hcoherent
      let candidate := seed.addEquality addedLeft addedRight
      have hcandidateNodup : AssignmentsNodup candidate := by
        simpa [candidate, AssignmentsNodup, Bindings.addEquality] using
          hseedNodup
      have hcandidateOut : BindingSubrecord candidate result :=
        mergeRel_left_subrecord hmerge
      have hcandidateTarget := hcandidateOut.trans hout
      by_cases hsourceJoined : source.1 ∈ out.eqClass addedLeft
      · have hall : ∀ value ∈ first :: rest,
            AtomDependenciesBelow out source value := by
          intro value hvalue
          exact addEquality_classValue_dependenciesBelow
            hseedNodup hvalues hcandidateTarget hnonvariable source
            hsourceJoined hvalue
        have hmatchedScope := matchListAccRel_dependenciesBelow
          hloopFree hnonvariable hsmaller hlist
          (by
            intro value hmem
            rcases List.mem_replicate.mp hmem with ⟨_, hvalue⟩
            subst value
            exact hall first (by simp))
          (by
            intro value hmem
            exact hall value (by simp [hmem]))
          (BindingDependenciesBelow.empty out source)
        have hmatchedSatisfied :=
          mergeRel_right_satisfied_of_dependenciesBelow
            hloopFree hnonvariable hsmaller hmerge hout hmatchedScope
        have hitems :=
          (HumanMatchSolutionTheory.matchListAccRel_solution_iff
            hlist valuation).mp hmatchedSatisfied |>.2
        have hpivot : ∀ value ∈ first :: rest,
            applyClassSolution valuation (toLeaTTaAtom first) =
              applyClassSolution valuation (toLeaTTaAtom value) := by
          apply map_replicate_eq_each
            (fun atom => applyClassSolution valuation (toLeaTTaAtom atom))
            first rest
          simpa [solutionTheory_toLeaTTaAtoms_eq_map,
            List.map_map, Function.comp_def] using hitems
        have hcandidateCoherent := evalCoherentIn_addEquality_of_pivot
          hcoherent hseedNodup hvalues hcandidateTarget hpivot
        exact ihMerge hout hcandidateNodup hcandidateCoherent
      · have hcandidateCoherent :=
          evalCoherentIn_addEquality_of_ambient_outside
            hcoherent hcandidateTarget hsourceJoined
        exact ihMerge hout hcandidateNodup hcandidateCoherent
  next =>
      intro seed hout hseedNodup hcoherent
      exact ⟨hcoherent, hseedNodup⟩
  next =>
      intro seed next result key value rest hadd htail ihAdd ihTail
        hout hseedNodup hcoherent
      have hnextOut := mergeConstraintsRel_seed_subrecord htail
      obtain ⟨hnextCoherent, hnextNodup⟩ :=
        ihAdd (hnextOut.trans hout) hseedNodup hcoherent
      exact ihTail hout hnextNodup hnextCoherent
  next =>
      intro seed next result addedLeft addedRight rest hadd htail
        ihAdd ihTail hout hseedNodup hcoherent
      have hnextOut := mergeConstraintsRel_seed_subrecord htail
      obtain ⟨hnextCoherent, hnextNodup⟩ :=
        ihAdd (hnextOut.trans hout) hseedNodup hcoherent
      exact ihTail hout hnextNodup hnextCoherent
  next =>
      intro mergedLeft mergedRight result order horder hfold ihFold
        hout hleftNodup hcoherent
      exact ihFold hout hleftNodup hcoherent
  · exact BindingSubrecord.refl out
  · exact humanMatch_assignmentsNodup hmatch

/-- Every successful executable-independent human match has coherent final
classes in its canonical valuation.  The proof is well-founded on semantic
class dependencies.  At each frontier, the derivation-local replay theorem
above equates the selected class value with every other stored value in that
same class. -/
theorem humanMatch_canonicalClassCoherent
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree out)
    (hnonvariable : AssignmentsNonVariable out) :
    CanonicalClassCoherent out hloopFree hnonvariable := by
  unfold CanonicalClassCoherent
  intro source
  apply (dependencyOrder_wellFounded hloopFree).induction source
  intro source hsmaller assignment
  cases hchosen : chosenClassAssignment out source.1 with
  | none =>
      have hnonempty : Nonempty (ClassAssignment out source.1) :=
        ⟨assignment⟩
      simp [chosenClassAssignment, hnonempty] at hchosen
  | some chosen =>
      have hchosenToAssignment : assignment.1.1 ∈
          out.eqClass chosen.1.1 := by
        have hchosenClass := chosen.2.2
        have hassignmentClass := assignment.2.2
        rw [EqualityClosure.mem_eqClass_iff_reachable]
          at hchosenClass hassignmentClass ⊢
        exact hchosenClass.symm.trans hassignmentClass
      have hagree := (humanMatch_evalCoherentAt
        hmatch hloopFree hnonvariable source hsmaller).values
          chosen.2.1 assignment.2.1 hchosenToAssignment chosen.2.2
      exact (canonicalNodeValue_eq_applyClassSolution_of_chosen
        hloopFree hnonvariable chosen hchosen).trans hagree

/-- Consequently every successful executable-independent human match has a
concrete canonical model. -/
theorem humanMatch_has_model
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hloopFree : HumanMatchMergeSpec.SemanticLoopFree out)
    (hnonvariable : AssignmentsNonVariable out) :
    ∃ valuation : String → Metta.Atom,
      HEBindingSatisfied valuation out := by
  refine ⟨canonicalValuation out hloopFree hnonvariable, ?_⟩
  exact canonicalValuation_satisfies_of_classCoherent
    hloopFree hnonvariable
    (humanMatch_canonicalClassCoherent hmatch hloopFree hnonvariable)

/-- The only genuinely recursive premise left by the guarded class invariant:
when equality insertion joins a class with disagreeing values, the recursive
list match followed by merge-back must expose a pivot path to every value in
that joined class.  Given this local equation-realization fact, the full
six-relation derivation preserves guarded class reconciliation. -/
theorem humanMatch_pathReconciled_of_reconcilePaths
    (hreconcilePaths : ∀
      {bindings : Bindings} {left right : String}
      {first : Atom} {rest : List Atom} {matched out : Bindings},
      AssignmentsNodup bindings →
      (first :: rest).Perm
        ((bindings.addEquality left right).classValues left) →
      HumanMatchMergeSpec.MatchListAccRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          (List.replicate rest.length first) rest
          Bindings.empty matched →
      HumanMatchMergeSpec.MergeRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          (bindings.addEquality left right) matched out →
      ∀ {target : Bindings},
        AssignmentsNonVariable target →
        BindingSubrecord out target →
        ∀ (source : DependencyNode target),
          source.1 ∈ target.eqClass left →
          ∀ value ∈ first :: rest,
            AtomReconciliationPath target source first value)
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hnonvariable : AssignmentsNonVariable out) :
    ClassAssignmentsPathReconciled out := by
  apply HumanMatchMergeSpec.MatchRel.rec
    (motive_1 := fun _ _ result _ =>
      AssignmentsNonVariable result →
        ClassAssignmentsPathReconciled result)
    (motive_2 := fun _ _ seed result _ =>
      ∀ target,
        AssignmentsNonVariable target →
        BindingSubrecord result target →
        AssignmentsNodup seed →
        ClassAssignmentsPathReconciledIn target seed →
          ClassAssignmentsPathReconciledIn target result ∧
            AssignmentsNodup result)
    (motive_3 := fun seed _ _ result _ =>
      ∀ target,
        AssignmentsNonVariable target →
        BindingSubrecord result target →
        AssignmentsNodup seed →
        ClassAssignmentsPathReconciledIn target seed →
          ClassAssignmentsPathReconciledIn target result ∧
            AssignmentsNodup result)
    (motive_4 := fun seed _ _ result _ =>
      ∀ target,
        AssignmentsNonVariable target →
        BindingSubrecord result target →
        AssignmentsNodup seed →
        ClassAssignmentsPathReconciledIn target seed →
          ClassAssignmentsPathReconciledIn target result ∧
            AssignmentsNodup result)
    (motive_5 := fun seed _ result _ =>
      ∀ target,
        AssignmentsNonVariable target →
        BindingSubrecord result target →
        AssignmentsNodup seed →
        ClassAssignmentsPathReconciledIn target seed →
          ClassAssignmentsPathReconciledIn target result ∧
            AssignmentsNodup result)
    (motive_6 := fun left _ result _ =>
      ∀ target,
        AssignmentsNonVariable target →
        BindingSubrecord result target →
        AssignmentsNodup left →
        ClassAssignmentsPathReconciledIn target left →
          ClassAssignmentsPathReconciledIn target result ∧
            AssignmentsNodup result)
    (t := hmatch)
  next =>
      intro symbol hadmissible hnonvariable
      apply pathReconciled_of_subsingleton_classAssignments hnonvariable
      apply classAssignments_subsingleton_of_assignments_unique
      intro left hleft
      simp [Bindings.empty] at hleft
  next =>
      intro leftName rightName hadmissible hnonvariable
      apply pathReconciled_of_subsingleton_classAssignments hnonvariable
      apply classAssignments_subsingleton_of_assignments_unique
      intro left hleft
      simp [Bindings.empty, Bindings.addEquality] at hleft
  next =>
      intro varName value hvalue hadmissible hnonvariable
      apply pathReconciled_of_subsingleton_classAssignments hnonvariable
      apply classAssignments_subsingleton_of_assignments_unique
      intro left hleft right hright
      have hleftEq : left = (varName, value) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hleft
      have hrightEq : right = (varName, value) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hright
      exact hleftEq.trans hrightEq.symm
  next =>
      intro value varName hvalue hadmissible hnonvariable
      apply pathReconciled_of_subsingleton_classAssignments hnonvariable
      apply classAssignments_subsingleton_of_assignments_unique
      intro left hleft right hright
      have hleftEq : left = (varName, value) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hleft
      have hrightEq : right = (varName, value) := by
        simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
          Bindings.lookup] using hright
      exact hleftEq.trans hrightEq.symm
  next =>
      intro lefts rights result hitems hadmissible ih hnonvariable
      have hemptyNodup : AssignmentsNodup Bindings.empty := by
        simp [AssignmentsNodup, Bindings.empty]
      exact (ih result hnonvariable (BindingSubrecord.refl result)
        hemptyNodup (pathReconciledIn_empty result)).1.toFinal
  next =>
      intro grounded right result hright hcustom hground hadmissible
        hnonvariable
      rcases hground with ⟨hrightEq, houtEq⟩
      subst right
      subst result
      apply pathReconciled_of_subsingleton_classAssignments hnonvariable
      apply classAssignments_subsingleton_of_assignments_unique
      intro left hleft
      simp [Bindings.empty] at hleft
  next =>
      intro left grounded result hleft hleftNoCustom hcustom hground
        hadmissible hnonvariable
      rcases hground with ⟨hleftEq, houtEq⟩
      subst left
      subst result
      apply pathReconciled_of_subsingleton_classAssignments hnonvariable
      apply classAssignments_subsingleton_of_assignments_unique
      intro left hleft
      simp [Bindings.empty] at hleft
  next =>
      intro left right hleft hright hadmissible hnonvariable
      exact (hleft (by
        simp [HumanMatchMergeSpec.equalityGroundedSemantic])).elim
  next =>
      intro seed target htargetNonvariable hout hseedNodup hreconciled
      exact ⟨hreconciled, hseedNodup⟩
  next =>
      intro left right lefts rights seed matched next result
        hhead hmerge htail ihHead ihMerge ihTail
        target htargetNonvariable hout hseedNodup hreconciled
      have hnextOut := matchListAccRel_seed_subrecord htail
      obtain ⟨hnextReconciled, hnextNodup⟩ :=
        ihMerge target htargetNonvariable (hnextOut.trans hout)
          hseedNodup hreconciled
      exact ihTail target htargetNonvariable hout
        hnextNodup hnextReconciled
  next =>
      intro seed varName value hvalues
        target htargetNonvariable hout hseedNodup hreconciled
      exact ⟨pathReconciledIn_assign_of_classValues_nil
          hreconciled htargetNonvariable hseedNodup hvalues hout,
        assignmentsNodup_assign hseedNodup⟩
  next =>
      intro seed varName value first rest hvalues hagree hvalue
        target htargetNonvariable hout hseedNodup hreconciled
      exact ⟨hreconciled, hseedNodup⟩
  next =>
      intro seed varName value first rest matched result hvalues hagree
        hne hhead hmerge ihHead ihMerge
        target htargetNonvariable hout hseedNodup hreconciled
      exact ihMerge target htargetNonvariable hout hseedNodup hreconciled
  next =>
      intro seed varName value first rest matched result hvalues hnotAgree
        hlist hmerge ihList ihMerge
        target htargetNonvariable hout hseedNodup hreconciled
      exact ihMerge target htargetNonvariable hout hseedNodup hreconciled
  next =>
      intro seed left right values hvalues hagree
        target htargetNonvariable hout hseedNodup hreconciled
      have hagree' : HumanMatchMergeSpec.ValuesAgree
          ((seed.addEquality left right).classValues left) := by
        rw [hvalues]
        exact hagree
      exact ⟨pathReconciledIn_addEquality_of_valuesAgree
          hreconciled htargetNonvariable hseedNodup hagree' hout,
        by simpa [AssignmentsNodup, Bindings.addEquality] using hseedNodup⟩
  next =>
      intro seed left right first rest matched result hvalues hnotAgree
        hlist hmerge ihList ihMerge
        target htargetNonvariable hout hseedNodup hreconciled
      let candidate := seed.addEquality left right
      have hcandidateNodup : AssignmentsNodup candidate := by
        simpa [candidate, AssignmentsNodup, Bindings.addEquality] using
          hseedNodup
      have hcandidateOut : BindingSubrecord candidate result :=
        mergeRel_left_subrecord hmerge
      have hcandidateTarget : BindingSubrecord candidate target :=
        hcandidateOut.trans hout
      have hpivotPaths : ∀ (source : DependencyNode target),
          source.1 ∈ target.eqClass left →
          ∀ value ∈ first :: rest,
            AtomReconciliationPath target source first value :=
        hreconcilePaths hseedNodup hvalues hlist hmerge
          htargetNonvariable hout
      have hcandidateReconciled :=
        pathReconciledIn_addEquality_of_pivotPaths
          hreconciled hseedNodup hvalues hcandidateTarget hpivotPaths
      exact ihMerge target htargetNonvariable hout
        hcandidateNodup hcandidateReconciled
  next =>
      intro seed target htargetNonvariable hout hseedNodup hreconciled
      exact ⟨hreconciled, hseedNodup⟩
  next =>
      intro seed next result varName value rest hadd htail ihAdd ihTail
        target htargetNonvariable hout hseedNodup hreconciled
      have hnextOut := mergeConstraintsRel_seed_subrecord htail
      obtain ⟨hnextReconciled, hnextNodup⟩ :=
        ihAdd target htargetNonvariable (hnextOut.trans hout)
          hseedNodup hreconciled
      exact ihTail target htargetNonvariable hout
        hnextNodup hnextReconciled
  next =>
      intro seed next result left right rest hadd htail ihAdd ihTail
        target htargetNonvariable hout hseedNodup hreconciled
      have hnextOut := mergeConstraintsRel_seed_subrecord htail
      obtain ⟨hnextReconciled, hnextNodup⟩ :=
        ihAdd target htargetNonvariable (hnextOut.trans hout)
          hseedNodup hreconciled
      exact ihTail target htargetNonvariable hout
        hnextNodup hnextReconciled
  next =>
      intro left right result order horder hfold ihFold
        target htargetNonvariable hout hleftNodup hreconciled
      exact ihFold target htargetNonvariable hout hleftNodup hreconciled
  exact hnonvariable

/-- A direct recursive-equation realization theorem is sufficient for the
guarded-path callback above.  All dependency guards are discharged from the
joined class's stored values; the remaining premise contains only the human
list-match and merge derivations and the direct `AtomsReconciled` conclusion. -/
theorem humanMatch_pathReconciled_of_reconcileAtoms
    (hreconcileAtoms : ∀
      {bindings : Bindings} {left right : String}
      {first : Atom} {rest : List Atom} {matched out : Bindings},
      HumanMatchMergeSpec.MatchListAccRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          (List.replicate rest.length first) rest
          Bindings.empty matched →
      HumanMatchMergeSpec.MergeRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          (bindings.addEquality left right) matched out →
      ∀ {target : Bindings},
        BindingSubrecord out target →
        AtomsReconciled target
          (List.replicate rest.length first) rest)
    {query pattern : Atom} {out : Bindings}
    (hmatch : HumanMatchMergeSpec.MatchRel
      HumanMatchMergeSpec.equalityGroundedSemantic query pattern out)
    (hnonvariable : AssignmentsNonVariable out) :
    ClassAssignmentsPathReconciled out := by
  apply humanMatch_pathReconciled_of_reconcilePaths
    (hmatch := hmatch) (hnonvariable := hnonvariable)
  intro bindings left right first rest matched merged
    hnodup hvalues hlist hmerge target htargetNonvariable hout
    source hsource value hvalue
  have hcandidateTarget : BindingSubrecord
      (bindings.addEquality left right) target :=
    (mergeRel_left_subrecord hmerge).trans hout
  have hfirstBelow := addEquality_classValue_dependenciesBelow
    hnodup hvalues hcandidateTarget htargetNonvariable source hsource
    (value := first) (by simp)
  have hvalueBelow := addEquality_classValue_dependenciesBelow
    hnodup hvalues hcandidateTarget htargetNonvariable source hsource hvalue
  have hitems := hreconcileAtoms hlist hmerge hout
  have hreconciled : AtomReconciled target first value := by
    simp only [List.mem_cons] at hvalue
    rcases hvalue with hvalue | hvalue
    · subst value
      exact AtomReconciled.refl target first
    · exact AtomsReconciled.each_of_replicate hitems value hvalue
  exact .step hfirstBelow hreconciled hvalueBelow

end Mettapedia.Languages.MeTTa.HE.HumanMatchStructuralModel
