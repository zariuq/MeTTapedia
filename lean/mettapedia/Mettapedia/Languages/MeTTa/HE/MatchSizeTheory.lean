import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# Structural size preservation for the HE matcher

The five mutually recursive executable matching functions never invent an
assignment value larger than the atoms already admitted by their caller.  This
is the structural descent fact needed when expression matching recursively
reconciles values carried by its live accumulator: Robinson fuel governs the
conflict worklist, while atom size governs recursive matcher calls.

The theorem is deliberately representation-insensitive.  It bounds only the
translated structural size of assignment payloads; equality order, class
representatives, and the particular reconciliation path are irrelevant.

The same semantic size measure proves that satisfied bindings with nonvariable
assignment payloads pass the independent specification's class-cycle boundary.
Variable occurrence and the structural model encoding are connected explicitly.

Finite matcher and merge completeness use that measure in this same owner.
The bounded construction produces actual HE declarative derivations, whose
existing execution completeness laws supply finite-depth occurrences. Cross
interpreter comparisons consume these facts downstream.
-/

namespace Mettapedia.Languages.MeTTa.HE.MatchSizeTheory

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Structural size of an HE atom in the shared finite-term model. -/
def HEAtomSize (atom : Atom) : Nat :=
  (encodeModelAtom atom).size

/-- Structural size after interpreting variables through a common solution.
Unlike raw syntax size, this measure sees a live class value as the semantic
subterm occupying its variable position. -/
def HESolutionAtomSize (valuation : String → Metta.Atom)
    (atom : Atom) : Nat :=
  (applyClassSolution valuation (encodeModelAtom atom)).size

/-- Every variable relation carried by a binding record lies below one
semantic ceiling.  Assignment entries record both the key and its payload;
equality entries record both endpoints.  The predicate is intentionally
independent of list order and equality-class representatives. -/
def HEBindingSolutionSizeBound (valuation : String → Metta.Atom)
    (b : Bindings) (bound : Nat) : Prop :=
  (∀ key value, (key, value) ∈ b.assignments →
    (valuation key).size < bound ∧
      HESolutionAtomSize valuation value < bound) ∧
  (∀ left right, (left, right) ∈ b.equalities →
    (valuation left).size < bound ∧ (valuation right).size < bound)

/-- Pointwise semantic-size ceiling for an atom list. -/
def HESolutionAtomsSizeBound (valuation : String → Metta.Atom)
    (atoms : List Atom) (bound : Nat) : Prop :=
  ∀ atom, atom ∈ atoms → HESolutionAtomSize valuation atom < bound

@[simp] theorem heSolutionAtomSize_var
    (valuation : String → Metta.Atom) (key : String) :
    HESolutionAtomSize valuation (.var key) = (valuation key).size := by
  simp [HESolutionAtomSize, encodeModelAtom, applyClassSolution]

/-! ## Satisfiable bindings and the semantic loop boundary -/

section SemanticLoopBoundary

open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (vars)

/-- The structural translation preserves the complete variable list, including repeated occurrences. -/
theorem encodeModelAtom_vars (atom : Atom) :
    (encodeModelAtom atom).vars = vars atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
    ((encodeModelAtoms atoms).map Metta.Atom.vars).flatten =
      vars.varsList atoms) with
  | symbol _ => simp [encodeModelAtom, Metta.Atom.vars, vars]
  | var _ => simp [encodeModelAtom, Metta.Atom.vars, vars]
  | grounded _ => simp [encodeModelAtom, Metta.Atom.vars, vars]
  | expression _ ih => simpa [encodeModelAtom, Metta.Atom.vars, vars] using ih
  | nil => rfl
  | cons head tail ihHead ihTail =>
      simp only [encodeModelAtoms, List.map_cons, List.flatten_cons,
        vars.varsList, ihHead, ihTail]

/-- Translated variable membership is exactly occurrence in the independent HE specification. -/
theorem mem_encodeModelAtom_vars_iff_atomOccurs {atom : Atom} {key : String} :
    key ∈ (encodeModelAtom atom).vars ↔ Spec.Match.Merge.AtomOccurs atom key := by
  rw [encodeModelAtom_vars]
  exact Spec.Match.Merge.mem_vars_iff_atomOccurs

/-- An occurrence below a nonvariable HE root is strictly smaller than the interpreted whole. -/
theorem size_valuation_lt_apply_of_atomOccurs_nonvariable
    (valuation : String → Metta.Atom) {value : Atom} {dependency : String}
    (hnonvariable : ∀ other, value ≠ .var other)
    (hoccurs : Spec.Match.Merge.AtomOccurs value dependency) :
    (valuation dependency).size < HESolutionAtomSize valuation value := by
  have htranslated : ∀ other, encodeModelAtom value ≠ .var other := by
    intro other
    cases value <;> simp_all [encodeModelAtom]
  exact size_valuation_lt_apply_of_mem_vars_nonvariable valuation htranslated
    (mem_encodeModelAtom_vars_iff_atomOccurs.mpr hoccurs)

/-- Every proper class dependency in a satisfied record with nonvariable assignment payloads strictly decreases valuation size. -/
theorem size_valuation_lt_of_heClassDepends
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hnonvariable : NoBareVarAssignments bindings)
    (hsatisfied : HEBindingSatisfied valuation bindings)
    {source target : String}
    (hdepends : Spec.Match.Merge.ClassDepends bindings source target) :
    (valuation target).size < (valuation source).size := by
  rcases hdepends with
    ⟨key, value, dependency, hassignment, hsource,
      hdependency, htarget, _hproper⟩
  have hnonvariableValue : ∀ other, value ≠ .var other := by
    intro other heq
    subst value
    exact hnonvariable hassignment
  have hproper := size_valuation_lt_apply_of_atomOccurs_nonvariable
    valuation hnonvariableValue hdependency
  have hsourceEq := hsatisfied.eq_of_mem_eqClass hsource
  have htargetEq := hsatisfied.eq_of_mem_eqClass htarget
  have hassignmentEq := hsatisfied.1 key value hassignment
  calc
    (valuation target).size = (valuation dependency).size :=
      congrArg Metta.Atom.size htargetEq.symm
    _ < (applyClassSolution valuation (encodeModelAtom value)).size := hproper
    _ = (valuation key).size := congrArg Metta.Atom.size hassignmentEq.symm
    _ = (valuation source).size := congrArg Metta.Atom.size hsourceEq

/-- A satisfying finite valuation excludes cycles among classes when every stored assignment payload is nonvariable. -/
theorem heSemanticLoopFree_of_satisfied_nonvariable
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    (hnonvariable : NoBareVarAssignments bindings) :
    Spec.Match.Merge.SemanticLoopFree bindings := by
  intro name hcycle
  have hstrictPath : ∀ {source target},
      Relation.TransGen (Spec.Match.Merge.ClassDepends bindings) source target →
        (valuation target).size < (valuation source).size := by
    intro source target path
    induction path with
    | single hstep =>
        exact size_valuation_lt_of_heClassDepends hnonvariable hsatisfied hstep
    | tail _ hlast ih =>
        exact (size_valuation_lt_of_heClassDepends hnonvariable hsatisfied hlast).trans ih
  exact Nat.lt_irrefl _ (hstrictPath hcycle)

/-- Lookup-level nonvariable values suffice when assignment keys are unique; uniqueness exposes every stored entry to lookup. -/
theorem heSemanticLoopFree_of_satisfied_noVarAssignmentValues
    {bindings : Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : HEBindingSatisfied valuation bindings)
    (hkeys : AssignmentsNodup bindings)
    (hnonvariable : NoVarAssignmentValues bindings) :
    Spec.Match.Merge.SemanticLoopFree bindings :=
  heSemanticLoopFree_of_satisfied_nonvariable hsatisfied
    (noBareVarAssignments_of_noVarAssignmentValues hkeys hnonvariable)

/-- A satisfied equation between a variable and a nonvariable atom excludes occurrence of that variable in the atom. -/
theorem not_atomOccurs_of_satisfied_nonvariable_equation
    {valuation : String → Metta.Atom} {key : String} {value : Atom}
    (hnonvariable : ∀ other, value ≠ .var other)
    (hequation : valuation key =
      applyClassSolution valuation (encodeModelAtom value)) :
    ¬Spec.Match.Merge.AtomOccurs value key := by
  intro hoccurs
  have hproper := size_valuation_lt_apply_of_atomOccurs_nonvariable
    valuation hnonvariable hoccurs
  change (valuation key).size <
    (applyClassSolution valuation (encodeModelAtom value)).size at hproper
  rw [← hequation] at hproper
  exact Nat.lt_irrefl _ hproper

end SemanticLoopBoundary

theorem HEBindingSolutionSizeBound.mono
    {valuation : String → Metta.Atom} {b : Bindings} {small large : Nat}
    (h : HEBindingSolutionSizeBound valuation b small)
    (hle : small ≤ large) :
    HEBindingSolutionSizeBound valuation b large := by
  constructor
  · intro key value hmem
    exact ⟨(h.1 key value hmem).1.trans_le hle,
      (h.1 key value hmem).2.trans_le hle⟩
  · intro left right hmem
    exact ⟨(h.2 left right hmem).1.trans_le hle,
      (h.2 left right hmem).2.trans_le hle⟩

theorem HESolutionAtomsSizeBound.mono
    {valuation : String → Metta.Atom} {atoms : List Atom}
    {small large : Nat}
    (h : HESolutionAtomsSizeBound valuation atoms small)
    (hle : small ≤ large) :
    HESolutionAtomsSizeBound valuation atoms large := by
  intro atom hmem
  exact (h atom hmem).trans_le hle

@[simp] theorem heBindingSolutionSizeBound_empty
    (valuation : String → Metta.Atom) (bound : Nat) :
    HEBindingSolutionSizeBound valuation Bindings.empty bound := by
  constructor <;> intro <;> simp [Bindings.empty] at *

theorem HEBindingSolutionSizeBound.addEquality
    {valuation : String → Metta.Atom} {b : Bindings} {bound : Nat}
    (h : HEBindingSolutionSizeBound valuation b bound)
    {left right : String}
    (hleft : (valuation left).size < bound)
    (hright : (valuation right).size < bound) :
    HEBindingSolutionSizeBound valuation
      (b.addEquality left right) bound := by
  constructor
  · intro key value hmem
    exact h.1 key value (by simpa [Bindings.addEquality] using hmem)
  · intro storedLeft storedRight hmem
    simp only [Bindings.addEquality, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hmem
    rcases hmem with hold | hnew
    · exact h.2 storedLeft storedRight hold
    · rcases hnew with ⟨rfl, rfl⟩
      exact ⟨hleft, hright⟩

theorem HEBindingSolutionSizeBound.assign
    {valuation : String → Metta.Atom} {b : Bindings} {bound : Nat}
    (h : HEBindingSolutionSizeBound valuation b bound)
    {key : String} {value : Atom}
    (hkey : (valuation key).size < bound)
    (hvalue : HESolutionAtomSize valuation value < bound) :
    HEBindingSolutionSizeBound valuation (b.assign key value) bound := by
  constructor
  · intro storedKey storedValue hmem
    by_cases hbound : b.isBound key = true
    · unfold Bindings.assign at hmem
      simp only [hbound, if_true] at hmem
      obtain ⟨binding, hbinding, hmap⟩ := List.mem_map.mp hmem
      rcases binding with ⟨oldKey, oldValue⟩
      by_cases hsame : oldKey = key
      · simp [hsame] at hmap
        rcases hmap with ⟨rfl, rfl⟩
        exact ⟨hkey, hvalue⟩
      · simp [hsame] at hmap
        rcases hmap with ⟨rfl, rfl⟩
        exact h.1 oldKey oldValue hbinding
    · have hbound' : b.isBound key = false := by
        cases hb : b.isBound key <;> simp_all
      unfold Bindings.assign at hmem
      simp only [hbound', Bool.false_eq_true, if_false] at hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact h.1 storedKey storedValue hold
      · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
        rcases hnew with ⟨rfl, rfl⟩
        exact ⟨hkey, hvalue⟩
  · intro left right hmem
    exact h.2 left right (by
      unfold Bindings.assign at hmem
      split at hmem <;> simpa using hmem)

theorem HESolutionAtomsSizeBound.tail
    {valuation : String → Metta.Atom} {atom : Atom} {atoms : List Atom}
    {bound : Nat}
    (h : HESolutionAtomsSizeBound valuation (atom :: atoms) bound) :
    HESolutionAtomsSizeBound valuation atoms bound := by
  intro child hchild
  exact h child (List.mem_cons_of_mem atom hchild)

theorem HESolutionAtomsSizeBound.head
    {valuation : String → Metta.Atom} {atom : Atom} {atoms : List Atom}
    {bound : Nat}
    (h : HESolutionAtomsSizeBound valuation (atom :: atoms) bound) :
    HESolutionAtomSize valuation atom < bound :=
  h atom (List.mem_cons_self ..)

theorem HESolutionAtomsSizeBound.replicate
    {valuation : String → Metta.Atom} {atom : Atom} {bound count : Nat}
    (h : HESolutionAtomSize valuation atom < bound) :
    HESolutionAtomsSizeBound valuation (List.replicate count atom) bound := by
  intro child hchild
  have : child = atom := List.eq_of_mem_replicate hchild
  simpa [this] using h

theorem HESolutionAtomsSizeBound.append
    {valuation : String → Metta.Atom} {left right : List Atom} {bound : Nat}
    (hleft : HESolutionAtomsSizeBound valuation left bound)
    (hright : HESolutionAtomsSizeBound valuation right bound) :
    HESolutionAtomsSizeBound valuation (left ++ right) bound := by
  intro atom hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft atom hmem
  · exact hright atom hmem

/-- Every assignment payload in `b` is strictly below `bound`. -/
def HEAssignmentsSizeBound (b : Bindings) (bound : Nat) : Prop :=
  ∀ key value, (key, value) ∈ b.assignments → HEAtomSize value < bound

/-- Every atom in a list is strictly below `bound`. -/
def HEAtomsSizeBound (atoms : List Atom) (bound : Nat) : Prop :=
  ∀ atom, atom ∈ atoms → HEAtomSize atom < bound

/-- A live-assignment bound remains valid when its numeric ceiling grows. -/
theorem HEAssignmentsSizeBound.mono
    {b : Bindings} {small large : Nat}
    (h : HEAssignmentsSizeBound b small) (hle : small ≤ large) :
    HEAssignmentsSizeBound b large := by
  intro key value hmem
  exact (h key value hmem).trans_le hle

/-- A pointwise atom-list bound remains valid when its ceiling grows. -/
theorem HEAtomsSizeBound.mono
    {atoms : List Atom} {small large : Nat}
    (h : HEAtomsSizeBound atoms small) (hle : small ≤ large) :
    HEAtomsSizeBound atoms large := by
  intro atom hmem
  exact (h atom hmem).trans_le hle

/-- Every finite atom list admits a strict common structural bound. -/
theorem exists_heAtomsSizeBound (atoms : List Atom) :
    ∃ bound, HEAtomsSizeBound atoms bound := by
  induction atoms with
  | nil =>
      exact ⟨0, by simp [HEAtomsSizeBound]⟩
  | cons atom atoms ih =>
      obtain ⟨tailBound, htail⟩ := ih
      let bound := max (HEAtomSize atom + 1) tailBound
      refine ⟨bound, ?_⟩
      intro value hmem
      rcases List.mem_cons.mp hmem with hhead | htailMem
      · subst value
        exact (Nat.lt_succ_self (HEAtomSize atom)).trans_le
          (Nat.le_max_left _ _)
      · exact (htail value htailMem).trans_le (Nat.le_max_right _ _)

/-- Every finite HE atom list admits a strict common-solution size ceiling
for any fixed valuation.  Unlike `exists_heAtomsSizeBound`, variables are
measured after valuation, which is the decreasing measure used by live
class-value reconciliation. -/
theorem exists_heSolutionAtomsSizeBound
    (valuation : String → Metta.Atom) (atoms : List Atom) :
    ∃ bound, HESolutionAtomsSizeBound valuation atoms bound := by
  induction atoms with
  | nil =>
      exact ⟨0, by simp [HESolutionAtomsSizeBound]⟩
  | cons atom atoms ih =>
      obtain ⟨tailBound, htail⟩ := ih
      let bound := max (HESolutionAtomSize valuation atom + 1) tailBound
      refine ⟨bound, ?_⟩
      intro value hmem
      rcases List.mem_cons.mp hmem with hhead | htailMem
      · subst value
        exact (Nat.lt_succ_self (HESolutionAtomSize valuation atom)).trans_le
          (Nat.le_max_left _ _)
      · exact (htail value htailMem).trans_le (Nat.le_max_right _ _)

/-- A finite record has one semantic-size ceiling for all of its assignment
keys, values and equality endpoints. No bound on the ambient valuation is
needed outside those finitely many constraints. -/
theorem exists_heBindingSolutionSizeBound
    (valuation : String → Metta.Atom) (bindings : Bindings) :
    ∃ bound, HEBindingSolutionSizeBound valuation bindings bound := by
  let atoms : List Atom := bindings.assignments.flatMap (fun entry => [.var entry.1,entry.2]) ++
    bindings.equalities.flatMap (fun entry => [.var entry.1,.var entry.2])
  obtain ⟨bound,covered⟩ := exists_heSolutionAtomsSizeBound valuation atoms
  refine ⟨bound,?_,?_⟩
  · intro key value member
    constructor
    · simpa only [heSolutionAtomSize_var] using covered (.var key)
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨(key,value),member,by simp⟩))
    · exact covered value
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨(key,value),member,by simp⟩))
  · intro left right member
    constructor
    · simpa only [heSolutionAtomSize_var] using covered (.var left)
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(left,right),member,by simp⟩))
    · simpa only [heSolutionAtomSize_var] using covered (.var right)
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(left,right),member,by simp⟩))

/-- Every finite HE binding record admits a strict bound on all assignment
payloads. -/
theorem exists_heAssignmentsSizeBound (b : Bindings) :
    ∃ bound, HEAssignmentsSizeBound b bound := by
  obtain ⟨bound, hbound⟩ :=
    exists_heAtomsSizeBound (b.assignments.map Prod.snd)
  refine ⟨bound, ?_⟩
  intro key value hmem
  exact hbound value (List.mem_map.mpr ⟨(key, value), hmem, rfl⟩)

@[simp] theorem heAssignmentsSizeBound_empty (bound : Nat) :
    HEAssignmentsSizeBound Bindings.empty bound := by
  intro key value h
  simp [Bindings.empty] at h

theorem HEAssignmentsSizeBound.addEquality
    {b : Bindings} {bound : Nat} (h : HEAssignmentsSizeBound b bound)
    (left right : String) :
    HEAssignmentsSizeBound (b.addEquality left right) bound := by
  intro key value hmem
  exact h key value (by simpa [Bindings.addEquality] using hmem)

theorem HEAssignmentsSizeBound.assign
    {b : Bindings} {bound : Nat} (h : HEAssignmentsSizeBound b bound)
    {key : String} {value : Atom} (hvalue : HEAtomSize value < bound) :
    HEAssignmentsSizeBound (b.assign key value) bound := by
  intro storedKey storedValue hmem
  by_cases hbound : b.isBound key = true
  · unfold Bindings.assign at hmem
    simp only [hbound, if_true] at hmem
    obtain ⟨binding, hbinding, hmap⟩ := List.mem_map.mp hmem
    rcases binding with ⟨oldKey, oldValue⟩
    by_cases hkey : oldKey = key
    · simp [hkey] at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact hvalue
    · simp [hkey] at hmap
      rcases hmap with ⟨rfl, rfl⟩
      exact h oldKey oldValue hbinding
  · have hbound' : b.isBound key = false := by
      cases hb : b.isBound key <;> simp_all
    unfold Bindings.assign at hmem
    simp only [hbound', Bool.false_eq_true, if_false] at hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · exact h storedKey storedValue hold
    · simp only [List.mem_singleton, Prod.mk.injEq] at hnew
      rcases hnew with ⟨rfl, rfl⟩
      exact hvalue

private theorem assignment_mem_of_lookup_eq_some
    {key : String} {value : Atom} :
    ∀ {assignments : List (String × Atom)},
      assignments.lookup key = some value → (key, value) ∈ assignments
  | [], h => by simp [List.lookup] at h
  | (storedKey, storedValue) :: rest, h => by
      rw [List.lookup] at h
      cases hkey : (key == storedKey) with
      | false =>
          rw [hkey] at h
          exact List.mem_cons_of_mem _ (assignment_mem_of_lookup_eq_some h)
      | true =>
          rw [hkey] at h
          have hkeys : key = storedKey := eq_of_beq hkey
          have hvalues : storedValue = value := Option.some.inj h
          subst hkeys
          subst hvalues
          exact List.mem_cons_self ..

theorem HEBindingSolutionSizeBound.classValue
    {valuation : String → Metta.Atom} {b : Bindings} {bound : Nat}
    (h : HEBindingSolutionSizeBound valuation b bound)
    {key : String} {value : Atom} (hvalue : value ∈ b.classValues key) :
    HESolutionAtomSize valuation value < bound := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with ⟨storedKey, _hclass, hlookup⟩
  exact (h.1 storedKey value
    (assignment_mem_of_lookup_eq_some (by
      simpa [Bindings.lookup] using hlookup))).2

/-- A class value is an assignment payload, so it inherits any assignment
size bound without inspecting equality-class order. -/
theorem HEAssignmentsSizeBound.classValue
    {b : Bindings} {bound : Nat} (h : HEAssignmentsSizeBound b bound)
    {key : String} {value : Atom} (hvalue : value ∈ b.classValues key) :
    HEAtomSize value < bound := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with ⟨storedKey, _hclass, hlookup⟩
  exact h storedKey value
    (assignment_mem_of_lookup_eq_some (by
      simpa [Bindings.lookup] using hlookup))

private theorem encodeModelAtoms_eq_map (atoms : List Atom) :
    encodeModelAtoms atoms = atoms.map encodeModelAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [encodeModelAtoms, ih]

/-- A child is strictly smaller than the expression containing it. -/
theorem mettaAtom_size_lt_expr_of_mem {atom : Metta.Atom}
    {atoms : List Metta.Atom} (hmem : atom ∈ atoms) :
    atom.size < (Metta.Atom.expr atoms).size := by
  simp only [Metta.Atom.size]
  simpa [Nat.add_comm] using Nat.lt_succ_of_le
    (List.single_le_sum (fun _ _ => Nat.zero_le _)
      atom.size (List.mem_map.mpr ⟨atom, hmem, rfl⟩))

/-- Translated HE expression children satisfy the same strict structural
descent. -/
theorem heAtomSize_lt_expression_of_mem {atom : Atom} {atoms : List Atom}
    (hmem : atom ∈ atoms) :
    HEAtomSize atom < HEAtomSize (.expression atoms) := by
  apply mettaAtom_size_lt_expr_of_mem
  rw [encodeModelAtoms_eq_map]
  exact List.mem_map.mpr ⟨atom, hmem, rfl⟩

/-- Interpreting variables preserves the strict child-of-expression size
descent.  This is the semantic measure needed when a live seed expands a
variable to a raw term as large as its enclosing syntax. -/
theorem heSolutionAtomSize_lt_expression_of_mem
    (valuation : String → Metta.Atom) {atom : Atom} {atoms : List Atom}
    (hmem : atom ∈ atoms) :
    HESolutionAtomSize valuation atom <
      HESolutionAtomSize valuation (.expression atoms) := by
  have htranslated : encodeModelAtom atom ∈ encodeModelAtoms atoms := by
    rw [encodeModelAtoms_eq_map]
    exact List.mem_map.mpr ⟨atom, hmem, rfl⟩
  have happly : applyClassSolution valuation (encodeModelAtom atom) ∈
      (encodeModelAtoms atoms).map (applyClassSolution valuation) :=
    List.mem_map.mpr ⟨encodeModelAtom atom, htranslated, rfl⟩
  have hstrict := mettaAtom_size_lt_expr_of_mem happly
  simpa [HESolutionAtomSize, encodeModelAtom, applyClassSolution] using hstrict

theorem heSolutionAtomsSizeBound_of_expression_lt
    (valuation : String → Metta.Atom) {atoms : List Atom} {bound : Nat}
    (h : HESolutionAtomSize valuation (.expression atoms) < bound) :
    HESolutionAtomsSizeBound valuation atoms bound := by
  intro atom hmem
  exact (heSolutionAtomSize_lt_expression_of_mem valuation hmem).trans h

/-- A satisfied live class value has exactly the semantic size of the
variable whose class exposes it. -/
theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEBindingSatisfied.solutionAtomSize_classValue
    {valuation : String → Metta.Atom} {b : Bindings}
    (h : HEBindingSatisfied valuation b)
    {key : String} {value : Atom} (hvalue : value ∈ b.classValues key) :
    HESolutionAtomSize valuation value = (valuation key).size := by
  unfold HESolutionAtomSize
  exact congrArg Metta.Atom.size
    (h.eq_applyClassSolution_of_mem_classValues hvalue).symm

theorem HEAtomsSizeBound.tail {atom : Atom} {atoms : List Atom} {bound : Nat}
    (h : HEAtomsSizeBound (atom :: atoms) bound) :
    HEAtomsSizeBound atoms bound := by
  intro child hchild
  exact h child (List.mem_cons_of_mem atom hchild)

theorem HEAtomsSizeBound.head {atom : Atom} {atoms : List Atom} {bound : Nat}
    (h : HEAtomsSizeBound (atom :: atoms) bound) :
    HEAtomSize atom < bound :=
  h atom (List.mem_cons_self ..)

theorem HEAtomsSizeBound.replicate {atom : Atom} {bound count : Nat}
    (h : HEAtomSize atom < bound) :
    HEAtomsSizeBound (List.replicate count atom) bound := by
  intro child hchild
  have : child = atom := List.eq_of_mem_replicate hchild
  simpa [this] using h

theorem HEAtomsSizeBound.append {left right : List Atom} {bound : Nat}
    (hleft : HEAtomsSizeBound left bound)
    (hright : HEAtomsSizeBound right bound) :
    HEAtomsSizeBound (left ++ right) bound := by
  intro atom hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft atom hmem
  · exact hright atom hmem

/-- Every child of an expression whose root is below `bound` is itself below
`bound`. -/
theorem heAtomsSizeBound_of_expression_lt {atoms : List Atom} {bound : Nat}
    (h : HEAtomSize (.expression atoms) < bound) :
    HEAtomsSizeBound atoms bound := by
  intro atom hmem
  exact (heAtomSize_lt_expression_of_mem hmem).trans h

/-! ## Fold plumbing for executable merge -/

private theorem stepFold_sizeBound {Entry : Type} {P : Entry → Prop}
    {step : Bindings → Entry → List Bindings} {bound : Nat}
    (hstep : ∀ {before : Bindings} {entry : Entry} {after : Bindings},
      after ∈ step before entry →
      HEAssignmentsSizeBound before bound → P entry →
      HEAssignmentsSizeBound after bound) :
    ∀ (entries : List Entry) (init : List Bindings) (out : Bindings),
      out ∈ entries.foldl
        (fun acc entry => acc.flatMap fun before => step before entry) init →
      (∀ seed ∈ init, HEAssignmentsSizeBound seed bound) →
      (∀ entry ∈ entries, P entry) →
      HEAssignmentsSizeBound out bound := by
  intro entries
  induction entries with
  | nil =>
      intro init out hout hinit _
      exact hinit out (by simpa using hout)
  | cons entry entries ih =>
      intro init out hout hinit hall
      rw [List.foldl_cons] at hout
      apply ih _ _ hout
      · intro after hafter
        obtain ⟨before, hbefore, hstepMem⟩ := List.mem_flatMap.mp hafter
        exact hstep hstepMem (hinit before hbefore)
          (hall entry (List.mem_cons_self ..))
      · intro later hlater
        exact hall later (List.mem_cons_of_mem entry hlater)

private theorem stepFold_solutionSizeBound
    {Entry : Type} {P : Entry → Prop}
    {valuation : String → Metta.Atom}
    {step : Bindings → Entry → List Bindings} {bound : Nat}
    (hstep : ∀ {before : Bindings} {entry : Entry} {after : Bindings},
      after ∈ step before entry →
      HEBindingSolutionSizeBound valuation before bound → P entry →
      HEBindingSolutionSizeBound valuation after bound) :
    ∀ (entries : List Entry) (init : List Bindings) (out : Bindings),
      out ∈ entries.foldl
        (fun acc entry => acc.flatMap fun before => step before entry) init →
      (∀ seed ∈ init,
        HEBindingSolutionSizeBound valuation seed bound) →
      (∀ entry ∈ entries, P entry) →
      HEBindingSolutionSizeBound valuation out bound := by
  intro entries
  induction entries with
  | nil =>
      intro init out hout hinit _
      exact hinit out (by simpa using hout)
  | cons entry entries ih =>
      intro init out hout hinit hall
      rw [List.foldl_cons] at hout
      apply ih _ _ hout
      · intro after hafter
        obtain ⟨before, hbefore, hstepMem⟩ := List.mem_flatMap.mp hafter
        exact hstep hstepMem (hinit before hbefore)
          (hall entry (List.mem_cons_self ..))
      · intro later hlater
        exact hall later (List.mem_cons_of_mem entry hlater)

/-! ## The five-function fuel induction -/

/-- Semantic counterpart of `sizeBoundPack`.  It tracks both assignment keys
and payloads and both equality endpoints.  This is the support invariant used
by the completeness recursion: a conflict may inspect an arbitrarily large
live seed, but every class value selected at a right-record key has the same
semantic ceiling as that key. -/
private theorem solutionSizeBoundPack
    (valuation : String → Metta.Atom) :
    ∀ fuel bound : Nat,
      (∀ {left right : Atom} {out : Bindings},
        out ∈ matchAtoms left right fuel →
        HESolutionAtomSize valuation left < bound →
        HESolutionAtomSize valuation right < bound →
        HEBindingSolutionSizeBound valuation out bound) ∧
      (∀ {lefts rights : List Atom} {acc : List Bindings} {out : Bindings},
        out ∈ matchAtomsList lefts rights acc fuel →
        HESolutionAtomsSizeBound valuation lefts bound →
        HESolutionAtomsSizeBound valuation rights bound →
        (∀ seed ∈ acc,
          HEBindingSolutionSizeBound valuation seed bound) →
        HEBindingSolutionSizeBound valuation out bound) ∧
      (∀ {left right out : Bindings},
        out ∈ mergeBindings left right fuel →
        HEBindingSolutionSizeBound valuation left bound →
        HEBindingSolutionSizeBound valuation right bound →
        HEBindingSolutionSizeBound valuation out bound) ∧
      (∀ {b : Bindings} {v : String} {value : Atom} {out : Bindings},
        out ∈ addVarBinding b v value fuel →
        HEBindingSolutionSizeBound valuation b bound →
        (valuation v).size < bound →
        HESolutionAtomSize valuation value < bound →
        HEBindingSolutionSizeBound valuation out bound) ∧
      (∀ {b : Bindings} {left right : String} {out : Bindings},
        out ∈ addVarEquality b left right fuel →
        HEBindingSolutionSizeBound valuation b bound →
        (valuation left).size < bound →
        (valuation right).size < bound →
        HEBindingSolutionSizeBound valuation out bound)
  | 0, _ => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro left right out h
        simp [matchAtoms] at h
      · intro lefts rights acc out h
        simp [matchAtomsList] at h
      · intro left right out h
        simp [mergeBindings] at h
      · intro b v value out h
        simp [addVarBinding] at h
      · intro b left right out h
        simp [addVarEquality] at h
  | fuel + 1, bound => by
      obtain ⟨ihA, ihB, ihC, ihD, ihE⟩ :=
        solutionSizeBoundPack valuation fuel bound
      have hD : ∀ {b : Bindings} {v : String} {value : Atom}
          {out : Bindings},
          out ∈ addVarBinding b v value (fuel + 1) →
          HEBindingSolutionSizeBound valuation b bound →
          (valuation v).size < bound →
          HESolutionAtomSize valuation value < bound →
          HEBindingSolutionSizeBound valuation out bound := by
        intro b v value out hout hb hkey hvalue
        simp only [addVarBinding] at hout
        split at hout
        · simp only [List.mem_singleton] at hout
          subst out
          exact hb.assign hkey hvalue
        · next first rest hclass =>
            split at hout
            · split at hout
              · simp only [List.mem_singleton] at hout
                simpa [hout] using hb
              · obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                have hfirst : HESolutionAtomSize valuation first < bound :=
                  hb.classValue (by
                    rw [hclass]
                    exact List.mem_cons_self ..)
                exact ihC hmerged hb (ihA hmatched hfirst hvalue)
            · obtain ⟨matched, hmatched, hmerged⟩ :=
                List.mem_flatMap.mp hout
              have hfirst : HESolutionAtomSize valuation first < bound :=
                hb.classValue (by
                  rw [hclass]
                  exact List.mem_cons_self ..)
              have hrest :
                  HESolutionAtomsSizeBound valuation rest bound := by
                intro atom hatom
                exact hb.classValue (by
                  rw [hclass]
                  exact List.mem_cons_of_mem first hatom)
              have hright : HESolutionAtomsSizeBound valuation
                  (rest ++ [value]) bound :=
                hrest.append (by
                  intro atom hatom
                  simp only [List.mem_singleton] at hatom
                  subst atom
                  exact hvalue)
              have hmatchedBound :
                  HEBindingSolutionSizeBound valuation matched bound :=
                ihB hmatched
                  (HESolutionAtomsSizeBound.replicate hfirst) hright
                  (by
                    intro seed hseed
                    simp only [List.mem_singleton] at hseed
                    subst seed
                    exact heBindingSolutionSizeBound_empty valuation bound)
              exact ihC hmerged hb hmatchedBound
      have hE : ∀ {b : Bindings} {left right : String} {out : Bindings},
          out ∈ addVarEquality b left right (fuel + 1) →
          HEBindingSolutionSizeBound valuation b bound →
          (valuation left).size < bound →
          (valuation right).size < bound →
          HEBindingSolutionSizeBound valuation out bound := by
        intro b left right out hout hb hleft hright
        simp only [addVarEquality] at hout
        split at hout
        · simp only [List.mem_singleton] at hout
          subst out
          exact hb.addEquality hleft hright
        · next hconsistent =>
            split at hout
            · simp at hout
            · next first second hclass =>
                obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                have hcandidate := hb.addEquality hleft hright
                have hfirst :
                    HESolutionAtomSize valuation first < bound :=
                  hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_self ..)
                have hsecond :
                    HESolutionAtomSize valuation second < bound :=
                  hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_of_mem first (List.mem_cons_self ..))
                exact ihC hmerged hcandidate
                  (ihA hmatched hfirst hsecond)
            · next first rest hnotPair hclass =>
                obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                have hcandidate := hb.addEquality hleft hright
                have hfirst :
                    HESolutionAtomSize valuation first < bound :=
                  hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_self ..)
                have hrest :
                    HESolutionAtomsSizeBound valuation rest bound := by
                  intro atom hatom
                  exact hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_of_mem first hatom)
                have hmatchedBound :
                    HEBindingSolutionSizeBound valuation matched bound :=
                  ihB hmatched
                    (HESolutionAtomsSizeBound.replicate hfirst) hrest
                    (by
                      intro seed hseed
                      simp only [List.mem_singleton] at hseed
                      subst seed
                      exact heBindingSolutionSizeBound_empty valuation bound)
                exact ihC hmerged hcandidate hmatchedBound
      have hC : ∀ {left right out : Bindings},
          out ∈ mergeBindings left right (fuel + 1) →
          HEBindingSolutionSizeBound valuation left bound →
          HEBindingSolutionSizeBound valuation right bound →
          HEBindingSolutionSizeBound valuation out bound := by
        intro left right out hout hleft hright
        simp only [mergeBindings] at hout
        have hafter : ∀ middle,
            middle ∈ right.assignments.foldl
              (fun acc entry => acc.flatMap fun before =>
                addVarBinding before entry.1 entry.2 fuel) [left] →
            HEBindingSolutionSizeBound valuation middle bound := by
          intro middle hmiddle
          exact stepFold_solutionSizeBound
            (step := fun before entry =>
              addVarBinding before entry.1 entry.2 fuel)
            (P := fun entry =>
              (valuation entry.1).size < bound ∧
                HESolutionAtomSize valuation entry.2 < bound)
            (fun hstep hbefore hentry =>
              ihD hstep hbefore hentry.1 hentry.2)
            right.assignments [left] middle hmiddle
            (by
              intro seed hseed
              simp only [List.mem_singleton] at hseed
              subst seed
              exact hleft)
            (by
              intro entry hentry
              exact hright.1 entry.1 entry.2 (by simpa using hentry))
        exact stepFold_solutionSizeBound
          (step := fun before entry =>
            addVarEquality before entry.1 entry.2 fuel)
          (P := fun entry =>
            (valuation entry.1).size < bound ∧
              (valuation entry.2).size < bound)
          (fun hstep hbefore hentry =>
            ihE hstep hbefore hentry.1 hentry.2)
          right.equalities _ out hout hafter
          (by
            intro entry hentry
            exact hright.2 entry.1 entry.2 (by simpa using hentry))
      have hB : ∀ {lefts rights : List Atom} {acc : List Bindings}
          {out : Bindings},
          out ∈ matchAtomsList lefts rights acc (fuel + 1) →
          HESolutionAtomsSizeBound valuation lefts bound →
          HESolutionAtomsSizeBound valuation rights bound →
          (∀ seed ∈ acc,
            HEBindingSolutionSizeBound valuation seed bound) →
          HEBindingSolutionSizeBound valuation out bound := by
        intro lefts rights acc out hout hlefts hrights hacc
        cases lefts <;> cases rights <;> simp [matchAtomsList] at hout
        case nil.nil => exact hacc out hout
        case cons.cons left lefts right rights =>
          apply ihB hout hlefts.tail hrights.tail
          intro next hnext
          obtain ⟨seed, hseed, hnext'⟩ := List.mem_flatMap.mp hnext
          obtain ⟨matched, hmatched, hmerged⟩ :=
            List.mem_flatMap.mp hnext'
          exact ihC hmerged (hacc seed hseed)
            (ihA hmatched hlefts.head hrights.head)
      have hA : ∀ {left right : Atom} {out : Bindings},
          out ∈ matchAtoms left right (fuel + 1) →
          HESolutionAtomSize valuation left < bound →
          HESolutionAtomSize valuation right < bound →
          HEBindingSolutionSizeBound valuation out bound := by
        intro left right out hout hleft hright
        cases left with
        | symbol leftName =>
            cases right with
            | symbol rightName =>
                by_cases hnames : leftName = rightName
                · subst hnames
                  simp [matchAtoms, getMetaType, Atom.symbolType] at hout
                  have : out = Bindings.empty := by simpa using hout.1
                  subst out
                  exact heBindingSolutionSizeBound_empty valuation bound
                · simp [matchAtoms, getMetaType, Atom.symbolType, hnames] at hout
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at hout
                have : out = Bindings.empty.assign rightName
                    (.symbol leftName) := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).assign
                  (by simpa using hright) hleft
            | grounded rightGround =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at hout
            | expression rightAtoms =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at hout
        | var leftName =>
            cases right with
            | symbol rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at hout
                have : out = Bindings.empty.assign leftName
                    (.symbol rightName) := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).assign
                  (by simpa using hleft) hright
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.variableType] at hout
                have : out = Bindings.empty.addEquality
                    leftName rightName := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).addEquality
                  (by simpa using hleft) (by simpa using hright)
            | grounded rightGround =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at hout
                have : out = Bindings.empty.assign leftName
                    (.grounded rightGround) := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).assign
                  (by simpa using hleft) hright
            | expression rightAtoms =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at hout
                have : out = Bindings.empty.assign leftName
                    (.expression rightAtoms) := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).assign
                  (by simpa using hleft) hright
        | grounded leftGround =>
            cases right with
            | symbol rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at hout
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at hout
                have : out = Bindings.empty.assign rightName
                    (.grounded leftGround) := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).assign
                  (by simpa using hright) hleft
            | grounded rightGround =>
                by_cases hgrounds : leftGround = rightGround
                · subst hgrounds
                  simp [matchAtoms, getMetaType, Atom.groundedType] at hout
                  have : out = Bindings.empty := by simpa using hout.1
                  subst out
                  exact heBindingSolutionSizeBound_empty valuation bound
                · simp [matchAtoms, getMetaType, Atom.groundedType,
                    hgrounds] at hout
            | expression rightAtoms =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at hout
        | expression leftAtoms =>
            cases right with
            | symbol rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at hout
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at hout
                have : out = Bindings.empty.assign rightName
                    (.expression leftAtoms) := by simpa using hout.1
                subst out
                exact (heBindingSolutionSizeBound_empty valuation bound).assign
                  (by simpa using hright) hleft
            | grounded rightGround =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at hout
            | expression rightAtoms =>
                by_cases hlength : leftAtoms.length = rightAtoms.length
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlength] at hout
                  exact ihB hout.1
                    (heSolutionAtomsSizeBound_of_expression_lt valuation hleft)
                    (heSolutionAtomsSizeBound_of_expression_lt valuation hright)
                    (by
                      intro seed hseed
                      simp only [List.mem_singleton] at hseed
                      subst seed
                      exact heBindingSolutionSizeBound_empty valuation bound)
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlength] at hout
      exact ⟨hA, hB, hC, hD, hE⟩

/-- The executable matcher, list matcher, merge, assignment insertion, and
equality insertion preserve one common strict assignment-payload bound.  The
shared-fuel induction is the operational invariant: recursive reconciliation
may reuse live accumulator values, but never creates a structurally larger
payload. -/
private theorem sizeBoundPack :
    ∀ fuel bound : Nat,
      (∀ {left right : Atom} {out : Bindings},
        out ∈ matchAtoms left right fuel →
        HEAtomSize left < bound → HEAtomSize right < bound →
        HEAssignmentsSizeBound out bound) ∧
      (∀ {lefts rights : List Atom} {acc : List Bindings} {out : Bindings},
        out ∈ matchAtomsList lefts rights acc fuel →
        HEAtomsSizeBound lefts bound →
        HEAtomsSizeBound rights bound →
        (∀ seed ∈ acc, HEAssignmentsSizeBound seed bound) →
        HEAssignmentsSizeBound out bound) ∧
      (∀ {left right out : Bindings},
        out ∈ mergeBindings left right fuel →
        HEAssignmentsSizeBound left bound →
        HEAssignmentsSizeBound right bound →
        HEAssignmentsSizeBound out bound) ∧
      (∀ {b : Bindings} {v : String} {value : Atom} {out : Bindings},
        out ∈ addVarBinding b v value fuel →
        HEAssignmentsSizeBound b bound →
        HEAtomSize value < bound →
        HEAssignmentsSizeBound out bound) ∧
      (∀ {b : Bindings} {left right : String} {out : Bindings},
        out ∈ addVarEquality b left right fuel →
        HEAssignmentsSizeBound b bound →
        HEAssignmentsSizeBound out bound)
  | 0, _ => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro left right out h
        simp [matchAtoms] at h
      · intro lefts rights acc out h
        simp [matchAtomsList] at h
      · intro left right out h
        simp [mergeBindings] at h
      · intro b v value out h
        simp [addVarBinding] at h
      · intro b left right out h
        simp [addVarEquality] at h
  | fuel + 1, bound => by
      obtain ⟨ihA, ihB, ihC, ihD, ihE⟩ := sizeBoundPack fuel bound
      have hD : ∀ {b : Bindings} {v : String} {value : Atom} {out : Bindings},
          out ∈ addVarBinding b v value (fuel + 1) →
          HEAssignmentsSizeBound b bound →
          HEAtomSize value < bound →
          HEAssignmentsSizeBound out bound := by
        intro b v value out hout hb hvalue
        simp only [addVarBinding] at hout
        split at hout
        · simp only [List.mem_singleton] at hout
          subst out
          exact hb.assign hvalue
        · next first rest hclass =>
            split at hout
            · split at hout
              · simp only [List.mem_singleton] at hout
                simpa [hout] using hb
              · obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                have hfirst : HEAtomSize first < bound :=
                  hb.classValue (by
                    rw [hclass]
                    exact List.mem_cons_self ..)
                exact ihC hmerged hb (ihA hmatched hfirst hvalue)
            · obtain ⟨matched, hmatched, hmerged⟩ :=
                List.mem_flatMap.mp hout
              have hfirst : HEAtomSize first < bound :=
                hb.classValue (by
                  rw [hclass]
                  exact List.mem_cons_self ..)
              have hrest : HEAtomsSizeBound rest bound := by
                intro atom hatom
                exact hb.classValue (by
                  rw [hclass]
                  exact List.mem_cons_of_mem first hatom)
              have hright : HEAtomsSizeBound (rest ++ [value]) bound :=
                hrest.append (by
                  intro atom hatom
                  simp only [List.mem_singleton] at hatom
                  subst atom
                  exact hvalue)
              have hmatchedBound : HEAssignmentsSizeBound matched bound :=
                ihB hmatched (HEAtomsSizeBound.replicate hfirst) hright
                  (by
                    intro seed hseed
                    simp only [List.mem_singleton] at hseed
                    subst seed
                    exact heAssignmentsSizeBound_empty bound)
              exact ihC hmerged hb hmatchedBound
      have hE : ∀ {b : Bindings} {left right : String} {out : Bindings},
          out ∈ addVarEquality b left right (fuel + 1) →
          HEAssignmentsSizeBound b bound →
          HEAssignmentsSizeBound out bound := by
        intro b left right out hout hb
        simp only [addVarEquality] at hout
        split at hout
        · simp only [List.mem_singleton] at hout
          subst out
          exact hb.addEquality left right
        · next hconsistent =>
            split at hout
            · simp at hout
            · next first second hclass =>
                obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                have hcandidate := hb.addEquality left right
                have hfirst : HEAtomSize first < bound :=
                  hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_self ..)
                have hsecond : HEAtomSize second < bound :=
                  hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_of_mem first (List.mem_cons_self ..))
                exact ihC hmerged hcandidate (ihA hmatched hfirst hsecond)
            · next first rest hnotPair hclass =>
                obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                have hcandidate := hb.addEquality left right
                have hfirst : HEAtomSize first < bound :=
                  hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_self ..)
                have hrest : HEAtomsSizeBound rest bound := by
                  intro atom hatom
                  exact hcandidate.classValue (by
                    rw [hclass]
                    exact List.mem_cons_of_mem first hatom)
                have hmatchedBound : HEAssignmentsSizeBound matched bound :=
                  ihB hmatched (HEAtomsSizeBound.replicate hfirst) hrest
                    (by
                      intro seed hseed
                      simp only [List.mem_singleton] at hseed
                      subst seed
                      exact heAssignmentsSizeBound_empty bound)
                exact ihC hmerged hcandidate hmatchedBound
      have hC : ∀ {left right out : Bindings},
          out ∈ mergeBindings left right (fuel + 1) →
          HEAssignmentsSizeBound left bound →
          HEAssignmentsSizeBound right bound →
          HEAssignmentsSizeBound out bound := by
        intro left right out hout hleft hright
        simp only [mergeBindings] at hout
        have hafter : ∀ middle,
            middle ∈ right.assignments.foldl
              (fun acc entry =>
                acc.flatMap fun before =>
                  addVarBinding before entry.1 entry.2 fuel) [left] →
            HEAssignmentsSizeBound middle bound := by
          intro middle hmiddle
          exact stepFold_sizeBound
            (step := fun before entry =>
              addVarBinding before entry.1 entry.2 fuel)
            (P := fun entry => HEAtomSize entry.2 < bound)
            (fun hstep hbefore hentry => ihD hstep hbefore hentry)
            right.assignments [left] middle hmiddle
            (by
              intro seed hseed
              simp only [List.mem_singleton] at hseed
              subst seed
              exact hleft)
            (by
              intro entry hentry
              exact hright entry.1 entry.2 (by simpa using hentry))
        exact stepFold_sizeBound
          (step := fun before entry =>
            addVarEquality before entry.1 entry.2 fuel)
          (P := fun _ => True)
          (fun hstep hbefore _ => ihE hstep hbefore)
          right.equalities _ out hout hafter (by simp)
      have hB : ∀ {lefts rights : List Atom} {acc : List Bindings}
          {out : Bindings},
          out ∈ matchAtomsList lefts rights acc (fuel + 1) →
          HEAtomsSizeBound lefts bound →
          HEAtomsSizeBound rights bound →
          (∀ seed ∈ acc, HEAssignmentsSizeBound seed bound) →
          HEAssignmentsSizeBound out bound := by
        intro lefts rights acc out hout hlefts hrights hacc
        cases lefts <;> cases rights <;> simp [matchAtomsList] at hout
        case nil.nil => exact hacc out hout
        case cons.cons left lefts right rights =>
          apply ihB hout hlefts.tail hrights.tail
          intro next hnext
          obtain ⟨seed, hseed, hnext'⟩ := List.mem_flatMap.mp hnext
          obtain ⟨matched, hmatched, hmerged⟩ :=
            List.mem_flatMap.mp hnext'
          exact ihC hmerged (hacc seed hseed)
            (ihA hmatched hlefts.head hrights.head)
      have hA : ∀ {left right : Atom} {out : Bindings},
          out ∈ matchAtoms left right (fuel + 1) →
          HEAtomSize left < bound → HEAtomSize right < bound →
          HEAssignmentsSizeBound out bound := by
        intro left right out hout hleft hright
        cases left with
        | symbol leftName =>
            cases right with
            | symbol rightName =>
                by_cases hnames : leftName = rightName
                · subst hnames
                  simp [matchAtoms, getMetaType, Atom.symbolType] at hout
                  have : out = Bindings.empty := by simpa using hout.1
                  subst out
                  exact heAssignmentsSizeBound_empty bound
                · simp [matchAtoms, getMetaType, Atom.symbolType, hnames] at hout
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at hout
                have : out = Bindings.empty.assign rightName (.symbol leftName) := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).assign hleft
            | grounded rightGround =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at hout
            | expression rightAtoms =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at hout
        | var leftName =>
            cases right with
            | symbol rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at hout
                have : out = Bindings.empty.assign leftName (.symbol rightName) := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).assign hright
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.variableType] at hout
                have : out = Bindings.empty.addEquality leftName rightName := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).addEquality _ _
            | grounded rightGround =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at hout
                have : out = Bindings.empty.assign leftName (.grounded rightGround) := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).assign hright
            | expression rightAtoms =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at hout
                have : out = Bindings.empty.assign leftName
                    (.expression rightAtoms) := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).assign hright
        | grounded leftGround =>
            cases right with
            | symbol rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at hout
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at hout
                have : out = Bindings.empty.assign rightName (.grounded leftGround) := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).assign hleft
            | grounded rightGround =>
                by_cases hgrounds : leftGround = rightGround
                · subst hgrounds
                  simp [matchAtoms, getMetaType, Atom.groundedType] at hout
                  have : out = Bindings.empty := by simpa using hout.1
                  subst out
                  exact heAssignmentsSizeBound_empty bound
                · simp [matchAtoms, getMetaType, Atom.groundedType,
                    hgrounds] at hout
            | expression rightAtoms =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at hout
        | expression leftAtoms =>
            cases right with
            | symbol rightName =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at hout
            | var rightName =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at hout
                have : out = Bindings.empty.assign rightName
                    (.expression leftAtoms) := by
                  simpa using hout.1
                subst out
                exact (heAssignmentsSizeBound_empty bound).assign hleft
            | grounded rightGround =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at hout
            | expression rightAtoms =>
                by_cases hlength : leftAtoms.length = rightAtoms.length
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlength] at hout
                  exact ihB hout.1
                    (heAtomsSizeBound_of_expression_lt hleft)
                    (heAtomsSizeBound_of_expression_lt hright)
                    (by
                      intro seed hseed
                      simp only [List.mem_singleton] at hseed
                      subst seed
                      exact heAssignmentsSizeBound_empty bound)
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlength] at hout
      exact ⟨hA, hB, hC, hD, hE⟩

/-! ## Public executable and relational consequences -/

theorem matchAtoms_solutionSizeBound
    {valuation : String → Metta.Atom}
    {left right : Atom} {out : Bindings} {fuel bound : Nat}
    (hout : out ∈ matchAtoms left right fuel)
    (hleft : HESolutionAtomSize valuation left < bound)
    (hright : HESolutionAtomSize valuation right < bound) :
    HEBindingSolutionSizeBound valuation out bound :=
  (solutionSizeBoundPack valuation fuel bound).1 hout hleft hright

theorem matchAtomsList_solutionSizeBound
    {valuation : String → Metta.Atom}
    {lefts rights : List Atom} {acc : List Bindings} {out : Bindings}
    {fuel bound : Nat}
    (hout : out ∈ matchAtomsList lefts rights acc fuel)
    (hlefts : HESolutionAtomsSizeBound valuation lefts bound)
    (hrights : HESolutionAtomsSizeBound valuation rights bound)
    (hacc : ∀ seed ∈ acc,
      HEBindingSolutionSizeBound valuation seed bound) :
    HEBindingSolutionSizeBound valuation out bound :=
  (solutionSizeBoundPack valuation fuel bound).2.1
    hout hlefts hrights hacc

theorem mergeBindings_solutionSizeBound
    {valuation : String → Metta.Atom}
    {left right out : Bindings} {fuel bound : Nat}
    (hout : out ∈ mergeBindings left right fuel)
    (hleft : HEBindingSolutionSizeBound valuation left bound)
    (hright : HEBindingSolutionSizeBound valuation right bound) :
    HEBindingSolutionSizeBound valuation out bound :=
  (solutionSizeBoundPack valuation fuel bound).2.2.1
    hout hleft hright

theorem matchRel_solutionSizeBound
    {valuation : String → Metta.Atom}
    {left right : Atom} {out : Bindings} {bound : Nat}
    (hout : DeclMatchSpec.MatchRel left right out)
    (hleft : HESolutionAtomSize valuation left < bound)
    (hright : HESolutionAtomSize valuation right < bound) :
    HEBindingSolutionSizeBound valuation out bound := by
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hout
  exact matchAtoms_solutionSizeBound hmem hleft hright

theorem mergeRel_solutionSizeBound
    {valuation : String → Metta.Atom}
    {left right out : Bindings} {bound : Nat}
    (hout : DeclMergeSpec.MergeRel left right out)
    (hleft : HEBindingSolutionSizeBound valuation left bound)
    (hright : HEBindingSolutionSizeBound valuation right bound) :
    HEBindingSolutionSizeBound valuation out bound := by
  obtain ⟨fuel, hmem⟩ := DeclMergeSpec.mergeBindings_complete hout
  exact mergeBindings_solutionSizeBound hmem hleft hright

theorem matchListAccRel_solutionSizeBound
    {valuation : String → Metta.Atom}
    {lefts rights : List Atom} {seed out : Bindings} {bound : Nat}
    (hout : DeclMatchSpec.MatchListAccRel lefts rights seed out)
    (hlefts : HESolutionAtomsSizeBound valuation lefts bound)
    (hrights : HESolutionAtomsSizeBound valuation rights bound)
    (hseed : HEBindingSolutionSizeBound valuation seed bound) :
    HEBindingSolutionSizeBound valuation out bound := by
  induction lefts generalizing rights seed out with
  | nil =>
      cases hout
      exact hseed
  | cons left lefts ih =>
      cases hout with
      | cons hmatch hmerge htail =>
          apply ih htail hlefts.tail hrights.tail
          exact mergeRel_solutionSizeBound
            (DeclMergeSpec.mergeBindings_sound hmerge)
            hseed
            (matchRel_solutionSizeBound hmatch hlefts.head hrights.head)

theorem matchAtoms_assignmentsSizeBound
    {left right : Atom} {out : Bindings} {fuel bound : Nat}
    (hout : out ∈ matchAtoms left right fuel)
    (hleft : HEAtomSize left < bound)
    (hright : HEAtomSize right < bound) :
    HEAssignmentsSizeBound out bound :=
  (sizeBoundPack fuel bound).1 hout hleft hright

theorem matchAtomsList_assignmentsSizeBound
    {lefts rights : List Atom} {acc : List Bindings} {out : Bindings}
    {fuel bound : Nat}
    (hout : out ∈ matchAtomsList lefts rights acc fuel)
    (hlefts : HEAtomsSizeBound lefts bound)
    (hrights : HEAtomsSizeBound rights bound)
    (hacc : ∀ seed ∈ acc, HEAssignmentsSizeBound seed bound) :
    HEAssignmentsSizeBound out bound :=
  (sizeBoundPack fuel bound).2.1 hout hlefts hrights hacc

theorem mergeBindings_assignmentsSizeBound
    {left right out : Bindings} {fuel bound : Nat}
    (hout : out ∈ mergeBindings left right fuel)
    (hleft : HEAssignmentsSizeBound left bound)
    (hright : HEAssignmentsSizeBound right bound) :
    HEAssignmentsSizeBound out bound :=
  (sizeBoundPack fuel bound).2.2.1 hout hleft hright

theorem addVarBinding_assignmentsSizeBound
    {b : Bindings} {v : String} {value : Atom} {out : Bindings}
    {fuel bound : Nat}
    (hout : out ∈ addVarBinding b v value fuel)
    (hb : HEAssignmentsSizeBound b bound)
    (hvalue : HEAtomSize value < bound) :
    HEAssignmentsSizeBound out bound :=
  (sizeBoundPack fuel bound).2.2.2.1 hout hb hvalue

theorem addVarEquality_assignmentsSizeBound
    {b : Bindings} {left right : String} {out : Bindings}
    {fuel bound : Nat}
    (hout : out ∈ addVarEquality b left right fuel)
    (hb : HEAssignmentsSizeBound b bound) :
    HEAssignmentsSizeBound out bound :=
  (sizeBoundPack fuel bound).2.2.2.2 hout hb

theorem matchRel_assignmentsSizeBound
    {left right : Atom} {out : Bindings} {bound : Nat}
    (hout : DeclMatchSpec.MatchRel left right out)
    (hleft : HEAtomSize left < bound)
    (hright : HEAtomSize right < bound) :
    HEAssignmentsSizeBound out bound := by
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hout
  exact matchAtoms_assignmentsSizeBound hmem hleft hright

theorem mergeRel_assignmentsSizeBound
    {left right out : Bindings} {bound : Nat}
    (hout : DeclMergeSpec.MergeRel left right out)
    (hleft : HEAssignmentsSizeBound left bound)
    (hright : HEAssignmentsSizeBound right bound) :
    HEAssignmentsSizeBound out bound := by
  obtain ⟨fuel, hmem⟩ := DeclMergeSpec.mergeBindings_complete hout
  exact mergeBindings_assignmentsSizeBound hmem hleft hright

/-- Declarative accumulator-threaded expression matching preserves the same
bound.  Each constructor exposes its from-empty child match and external live
merge separately, so no seed-extraction or merge-associativity lemma is
needed. -/
theorem matchListAccRel_assignmentsSizeBound
    {lefts rights : List Atom} {seed out : Bindings} {bound : Nat}
    (hout : DeclMatchSpec.MatchListAccRel lefts rights seed out)
    (hlefts : HEAtomsSizeBound lefts bound)
    (hrights : HEAtomsSizeBound rights bound)
    (hseed : HEAssignmentsSizeBound seed bound) :
    HEAssignmentsSizeBound out bound := by
  induction lefts generalizing rights seed out with
  | nil =>
      cases hout
      exact hseed
  | cons left lefts ih =>
      cases hout with
      | cons hmatch hmerge htail =>
          apply ih htail hlefts.tail hrights.tail
          exact mergeRel_assignmentsSizeBound
            (DeclMergeSpec.mergeBindings_sound hmerge)
            hseed
            (matchRel_assignmentsSizeBound hmatch hlefts.head hrights.head)

/-! ## Canaries -/

/-- POSITIVE: inserting a compound payload respects its immediate successor
bound. -/
example : HEAssignmentsSizeBound
    (Bindings.empty.assign "x" (.expression [.symbol "f", .var "y"]))
    (HEAtomSize (.expression [.symbol "f", .var "y"]) + 1) :=
  (heAssignmentsSizeBound_empty _).assign (Nat.lt_succ_self _)

/-- NEGATIVE: the strict bound cannot be weakened to admit a payload at the
bound itself. -/
example : ¬ HEAssignmentsSizeBound
    (Bindings.empty.assign "x" (.expression [.symbol "f", .var "y"]))
    (HEAtomSize (.expression [.symbol "f", .var "y"])) := by
  intro hbound
  have hmem : ("x", .expression [.symbol "f", .var "y"]) ∈
      (Bindings.empty.assign "x"
        (.expression [.symbol "f", .var "y"])).assignments := by
    simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]
  exact (Nat.lt_irrefl _) (hbound _ _ hmem)

/-- A proper dependency is admissible when its finite valuation satisfies it. -/
theorem satisfied_proper_dependency_is_loopFree : Spec.Match.Merge.SemanticLoopFree
    ⟨[("x", .expression [.var "y"])], []⟩ := by
  apply heSemanticLoopFree_of_satisfied_nonvariable
    (valuation := fun key => if key = "x" then .expr [.sym "a"] else .sym "a")
  · constructor
    · intro key value hmem
      have : key = "x" ∧ value = .expression [.var "y"] := by
        simpa using hmem
      rcases this with ⟨rfl, rfl⟩
      simp [applyClassSolution, encodeModelAtom, encodeModelAtoms]
    · intro left right hmem
      simp at hmem
  · intro key target hmem
    simp at hmem

/-- No finite valuation can solve a variable equated to an expression containing it. -/
theorem self_containing_equation_unsatisfied (valuation : String → Metta.Atom) :
    valuation "x" ≠ applyClassSolution valuation
      (encodeModelAtom (.expression [.var "x"])) := by
  intro heq
  exact not_atomOccurs_of_satisfied_nonvariable_equation (by simp) heq
    (.expression (by simp) (.var "x"))

/-- Lookup alone misses a shadowed self-assignment. Satisfiability therefore
needs pointwise nonvariable entries, or lookup plus key uniqueness. -/
theorem lookup_nonvariable_can_hide_satisfied_cycle :
    let bindings : Bindings :=
      ⟨[("x", .symbol "a"), ("x", .var "x")], []⟩
    HEBindingSatisfied (fun _ => .sym "a") bindings ∧
      NoVarAssignmentValues bindings ∧
      ¬Spec.Match.Merge.SemanticLoopFree bindings := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro key value hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [applyClassSolution, encodeModelAtom]
    · intro left right hmem
      simp at hmem
  · intro key target hlookup
    simp [Bindings.lookup, List.lookup] at hlookup
    split at hlookup <;> simp_all
  · intro hfree
    apply hfree "x" (.single ?_)
    refine ⟨"x", .var "x", "x", by simp, ?_, .var "x", ?_, ?_⟩
    · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
    · exact EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl
    · simp


/-! ## Finite semantic completeness of the HE matcher and merger -/

open Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)

/-- Translation of HE grounded payloads is injective. -/
private theorem encodeModelGround_injective :
    Function.Injective encodeModelGround := by
  intro left right heq
  cases left <;> cases right <;>
    simp [encodeModelGround] at heq <;> simp_all

theorem not_atomOccurs_of_varNonVar_equation
    {valuation : String → Metta.Atom} {key : String} {value : Atom}
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hequation : MettaEquationSatisfied valuation
      (encodeModelAtom (.var key), encodeModelAtom value)) :
    ¬ AtomOccurs value key := by
  apply not_atomOccurs_of_satisfied_nonvariable_equation
  · intro target hvar
    subst value
    simp [DeclMatchSpec.Atom.isVarB] at hnonvar
  · simpa [MettaEquationSatisfied, encodeModelAtom, applyClassSolution] using
      hequation

theorem not_atomOccurs_of_nonVarVar_equation
    {valuation : String → Metta.Atom} {key : String} {value : Atom}
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hequation : MettaEquationSatisfied valuation
      (encodeModelAtom value, encodeModelAtom (.var key))) :
    ¬ AtomOccurs value key :=
  not_atomOccurs_of_varNonVar_equation hnonvar hequation.symm

/-- A satisfying head equation yields a dispatch branch with the actual
head tags and its occurs-check guard. The variable/variable branch still
requires an authorization from the original constraint graph. -/
inductive ModelHeadCase (left right : Atom) : Prop where
  | symbols (name : String) (source : left = .symbol name) (target : right = .symbol name)
  | grounds (value : OSLFCore.GroundedValue) (source : left = .grounded value) (target : right = .grounded value)
  | assignLeft (key : String) (source : left = .var key)
      (nonvar : DeclMatchSpec.Atom.isVarB right = false) (occursFree : ¬ AtomOccurs right key)
  | assignRight (key : String) (target : right = .var key)
      (nonvar : DeclMatchSpec.Atom.isVarB left = false) (occursFree : ¬ AtomOccurs left key)
  | twoVariables (first second : String) (source : left = .var first) (target : right = .var second)
  | expressions (first second : List Atom)
      (source : left = .expression first) (target : right = .expression second)

theorem modelHeadCase_of_equation {valuation : String → Metta.Atom} {left right : Atom}
    (satisfied : MettaEquationSatisfied valuation (encodeModelAtom left, encodeModelAtom right)) :
    ModelHeadCase left right := by
  cases left with
  | symbol leftName =>
      cases right with
      | symbol rightName =>
          have same : leftName = rightName := by
            simpa [MettaEquationSatisfied, encodeModelAtom, applyClassSolution] using satisfied
          subst rightName
          exact .symbols leftName rfl rfl
      | var key => exact .assignRight key rfl rfl (not_atomOccurs_of_nonVarVar_equation rfl satisfied)
      | grounded _ | expression _ =>
          simp [MettaEquationSatisfied, encodeModelAtom, applyClassSolution] at satisfied
  | var key =>
      cases right with
      | var other => exact .twoVariables key other rfl rfl
      | symbol _ | grounded _ | expression _ =>
          exact .assignLeft key rfl rfl (not_atomOccurs_of_varNonVar_equation rfl satisfied)
  | grounded leftValue =>
      cases right with
      | grounded rightValue =>
          have same : leftValue = rightValue :=
            encodeModelGround_injective (by
              simpa [MettaEquationSatisfied, encodeModelAtom, applyClassSolution] using satisfied)
          subst rightValue
          exact .grounds leftValue rfl rfl
      | var key => exact .assignRight key rfl rfl (not_atomOccurs_of_nonVarVar_equation rfl satisfied)
      | symbol _ | expression _ =>
          simp [MettaEquationSatisfied, encodeModelAtom, applyClassSolution] at satisfied
  | expression first =>
      cases right with
      | expression second => exact .expressions first second rfl rfl
      | var key => exact .assignRight key rfl rfl (not_atomOccurs_of_nonVarVar_equation rfl satisfied)
      | symbol _ | grounded _ =>
          simp [MettaEquationSatisfied, encodeModelAtom, applyClassSolution] at satisfied

example : ModelHeadCase (.var "X") (.symbol "value") :=
  modelHeadCase_of_equation (valuation := fun _ => .sym "value") (by
    simp [MettaEquationSatisfied, encodeModelAtom, applyClassSolution])

example : ¬ ModelHeadCase (.symbol "left") (.symbol "right") := by
  intro classified
  cases classified <;> simp_all
  rename_i name source target
  exact (by decide : "left" ≠ "right") (source.trans target.symm)

/-- A semantically satisfiable HE leaf equation has a declarative matcher
witness.  Expression/expression equations are reserved for the paired list /
merge recursion. -/
theorem exists_matchRel_of_solution_leaf
    {left right : Atom}
    (hsat : ∃ valuation : String → Metta.Atom,
      MettaEquationSatisfied valuation
        (encodeModelAtom left, encodeModelAtom right))
    (hleaf : ¬ BothExpressions left right) :
    ∃ out, DeclMatchSpec.MatchRel left right out := by
  obtain ⟨valuation, hequation⟩ := hsat
  cases modelHeadCase_of_equation hequation with
  | symbols name leftShape rightShape =>
      subst left right
      exact ⟨Bindings.empty, .symSym name⟩
  | grounds value leftShape rightShape =>
      subst left right
      exact ⟨Bindings.empty, .grounded value⟩
  | assignLeft key leftShape nonvar occursFree =>
      subst left
      exact ⟨Bindings.empty.assign key right, .varNonVar nonvar occursFree⟩
  | assignRight key rightShape nonvar occursFree =>
      subst right
      exact ⟨Bindings.empty.assign key left, .nonVarVar nonvar occursFree⟩
  | twoVariables first second leftShape rightShape =>
      subst left right
      exact ⟨Bindings.empty.addEquality first second, .varVar first second⟩
  | expressions first second leftShape rightShape =>
      exact (hleaf ⟨first, second, leftShape, rightShape⟩).elim

/-- The semantic leaf witness is returned by the executable HE matcher at
some finite fuel. -/
theorem exists_matchAtoms_of_solution_leaf
    {left right : Atom}
    (hsat : ∃ valuation : String → Metta.Atom,
      MettaEquationSatisfied valuation
        (encodeModelAtom left, encodeModelAtom right))
    (hleaf : ¬ BothExpressions left right) :
    ∃ out fuel, out ∈ matchAtoms left right fuel := by
  obtain ⟨out, hrel⟩ := exists_matchRel_of_solution_leaf hsat hleaf
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hrel
  exact ⟨out, fuel, hmem⟩

private theorem heLookup_eq_some_of_assignment_mem_of_nodup
    {assignments : List (String × Atom)}
    (hkeys : (assignments.map Prod.fst).Nodup)
    {key : String} {value : Atom}
    (hmem : (key, value) ∈ assignments) :
    List.lookup key assignments = some value := by
  induction assignments with
  | nil => cases hmem
  | cons binding rest ih =>
      rcases binding with ⟨headKey, headValue⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      have hkeysTail : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        simp
      · have hheadFresh : headKey ∉ rest.map Prod.fst := by
          simpa using (List.nodup_cons.mp hkeys).1
        have hne : key ≠ headKey := by
          intro heq
          subst key
          exact hheadFresh (List.mem_map_of_mem htail)
        have hbeq : (key == headKey) = false := by simp [hne]
        simpa [List.lookup_cons, hbeq] using ih hkeysTail htail

/-- Every executable HE matcher output satisfies the no-bare-variable
assignment invariant used by recursive merge-back. -/
theorem heAssignmentsNonVariable_of_matchAtoms
    {left right : Atom} {out : Bindings} {fuel : Nat}
    (hmatch : out ∈ matchAtoms left right fuel) :
    HEAssignmentsNonVariable out := by
  intro key target hassignment
  have hlookup : out.lookup key = some (.var target) := by
    unfold Bindings.lookup
    exact heLookup_eq_some_of_assignment_mem_of_nodup
      (DeclMatchSpec.matchAtoms_assignmentsNodup hmatch) hassignment
  exact DeclMatchSpec.matchAtoms_noVarAssignmentValues hmatch hlookup

/-- Declarative matcher results have the same operational invariant. -/
theorem heAssignmentsNonVariable_of_matchRel
    {left right : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel left right out) :
    HEAssignmentsNonVariable out := by
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hmatch
  exact heAssignmentsNonVariable_of_matchAtoms hmem

/-- Consequently every value selected from any equality class is a
non-variable atom. -/
theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.HEAssignmentsNonVariable.isVarB_eq_false_of_classValue
    {b : Bindings} (h : HEAssignmentsNonVariable b)
    {key : String} {value : Atom}
    (hvalue : value ∈ b.classValues key) :
    DeclMatchSpec.Atom.isVarB value = false := by
  unfold Bindings.classValues at hvalue
  rcases List.mem_filterMap.mp hvalue with ⟨storedKey, _hclass, hlookup⟩
  apply h.isVarB_eq_false_of_assignment
  exact assignment_mem_of_lookup_eq_some (by
    simpa [Bindings.lookup] using hlookup)

/-- A successful HE leaf match between two non-variables is necessarily
reflexive.  Thus every unequal non-variable reconciliation that succeeds must
enter the expression/list recursion. -/
theorem matchAtoms_eq_of_nonvariable_leaf
    {left right : Atom} {out : Bindings} {fuel : Nat}
    (hleft : DeclMatchSpec.Atom.isVarB left = false)
    (hright : DeclMatchSpec.Atom.isVarB right = false)
    (hleaf : ¬ BothExpressions left right)
    (hmatch : out ∈ matchAtoms left right fuel) :
    left = right := by
  have hrel := DeclMatchSpec.matchAtoms_sound hmatch
  cases hrel with
  | symSym => rfl
  | varVar => simp [DeclMatchSpec.Atom.isVarB] at hleft
  | varNonVar => simp [DeclMatchSpec.Atom.isVarB] at hleft
  | nonVarVar => simp [DeclMatchSpec.Atom.isVarB] at hright
  | grounded => rfl
  | expr => exact (hleaf (by simp [BothExpressions])).elim

/-- Any two values already carried by one satisfying HE equality class have
the same valuation image. -/
theorem classValues_equationSatisfied
    {before : Bindings} {valuation : String → Metta.Atom}
    {key : String} {first second : Atom}
    (hbefore : HEBindingSatisfied valuation before)
    (hfirst : first ∈ before.classValues key)
    (hsecond : second ∈ before.classValues key) :
    MettaEquationSatisfied valuation
      (encodeModelAtom first, encodeModelAtom second) := by
  have hfirstValue :=
    hbefore.eq_applyClassSolution_of_mem_classValues hfirst
  have hsecondValue :=
    hbefore.eq_applyClassSolution_of_mem_classValues hsecond
  exact hfirstValue.symm.trans hsecondValue

/-- A satisfying class and one co-satisfied proposed value validate the exact
replicate/append list equation used by `AddVarBindingRel.reconcile`.  This is
purely the semantic input to the original pointwise matcher; it asserts no
matcher or merge existence. -/
theorem classValues_reconcileList_satisfied
    {valuation : String → Metta.Atom} {before : Bindings}
    {key : String} {first value : Atom} {rest : List Atom}
    (hbefore : HEBindingSatisfied valuation before)
    (hclass : before.classValues key = first :: rest)
    (hvalue : valuation key =
      applyClassSolution valuation (encodeModelAtom value)) :
    MettaAtomListsSatisfied valuation
      (encodeModelAtoms (List.replicate (rest.length + 1) first))
      (encodeModelAtoms (rest ++ [value])) := by
  have hfirstMem : first ∈ before.classValues key := by
    rw [hclass]
    simp
  have hfirstValue : valuation key =
      applyClassSolution valuation (encodeModelAtom first) :=
    hbefore.eq_applyClassSolution_of_mem_classValues hfirstMem
  have hrestValue : ∀ other ∈ rest,
      applyClassSolution valuation (encodeModelAtom other) =
        applyClassSolution valuation (encodeModelAtom first) := by
    intro other hmem
    have hotherMem : other ∈ before.classValues key := by
      rw [hclass]
      simp [hmem]
    have hotherValue :=
      hbefore.eq_applyClassSolution_of_mem_classValues hotherMem
    exact hotherValue.symm.trans hfirstValue
  have hlast : applyClassSolution valuation (encodeModelAtom value) =
      applyClassSolution valuation (encodeModelAtom first) :=
    hvalue.symm.trans hfirstValue
  have go : ∀ xs : List Atom,
      (∀ other ∈ xs,
        applyClassSolution valuation (encodeModelAtom other) =
          applyClassSolution valuation (encodeModelAtom first)) →
      MettaAtomListsSatisfied valuation
        (encodeModelAtoms (List.replicate (xs.length + 1) first))
        (encodeModelAtoms (xs ++ [value])) := by
    intro xs hall
    induction xs with
    | nil =>
        simpa [MettaAtomListsSatisfied, encodeModelAtoms] using hlast.symm
    | cons other tail ih =>
        have hother := hall other (by simp)
        have htail : ∀ item ∈ tail,
            applyClassSolution valuation (encodeModelAtom item) =
              applyClassSolution valuation (encodeModelAtom first) := by
          intro item hmem
          exact hall item (by simp [hmem])
        simpa [MettaAtomListsSatisfied, encodeModelAtoms,
          List.replicate_succ, hother] using ih htail
  exact go rest hrestValue

/-- Pointwise equality of one class representative with every remaining
class value.  This is the semantic input to the original class-wide HE list
matcher; it makes no matcher-existence claim. -/
theorem classValues_replicateTail_satisfied
    {valuation : String → Metta.Atom} {b : Bindings}
    {key : String} {first : Atom} {rest : List Atom}
    (hbinding : HEBindingSatisfied valuation b)
    (hclass : b.classValues key = first :: rest) :
    MettaAtomListsSatisfied valuation
      (encodeModelAtoms (List.replicate rest.length first))
      (encodeModelAtoms rest) := by
  have hfirstMem : first ∈ b.classValues key := by
    rw [hclass]
    simp
  have hfirst :=
    hbinding.eq_applyClassSolution_of_mem_classValues hfirstMem
  have hall : ∀ other ∈ rest,
      applyClassSolution valuation (encodeModelAtom other) =
        applyClassSolution valuation (encodeModelAtom first) := by
    intro other hmem
    have hotherMem : other ∈ b.classValues key := by
      rw [hclass]
      simp [hmem]
    have hother :=
      hbinding.eq_applyClassSolution_of_mem_classValues hotherMem
    exact hother.symm.trans hfirst
  have go : ∀ xs : List Atom,
      (∀ other ∈ xs,
        applyClassSolution valuation (encodeModelAtom other) =
          applyClassSolution valuation (encodeModelAtom first)) →
      MettaAtomListsSatisfied valuation
        (encodeModelAtoms (List.replicate xs.length first))
        (encodeModelAtoms xs) := by
    intro xs hxs
    induction xs with
    | nil => simp [MettaAtomListsSatisfied, encodeModelAtoms]
    | cons other tail ih =>
        have hother := hxs other (by simp)
        have htail : ∀ item ∈ tail,
            applyClassSolution valuation (encodeModelAtom item) =
              applyClassSolution valuation (encodeModelAtom first) := by
          intro item hmem
          exact hxs item (by simp [hmem])
        simpa [MettaAtomListsSatisfied, encodeModelAtoms,
          List.replicate_succ, hother] using ih htail
  exact go rest hall

/-- An unequal non-variable value already carried by a satisfying HE class
and any co-satisfied proposed value must form an expression/expression pair.
This is the representation-free entry condition for the direct conflict
branch: it uses the common valuation and the original HE leaf matcher only to
exclude an impossible unequal leaf. -/
theorem bothExpressions_of_ne_classValue_coSatisfied
    {valuation : String → Metta.Atom} {before : Bindings}
    {key : String} {first value : Atom} {rest : List Atom}
    (hbinding : HEBindingSatisfied valuation before)
    (hnonvar : HEAssignmentsNonVariable before)
    (hclass : before.classValues key = first :: rest)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hvalue : valuation key =
      applyClassSolution valuation (encodeModelAtom value))
    (hne : first ≠ value) :
    BothExpressions first value := by
  have hfirstMem : first ∈ before.classValues key := by
    rw [hclass]
    simp
  have hfirstNonvar : DeclMatchSpec.Atom.isVarB first = false :=
    hnonvar.isVarB_eq_false_of_classValue hfirstMem
  have hfirstValue :=
    hbinding.eq_applyClassSolution_of_mem_classValues hfirstMem
  have hequation : MettaEquationSatisfied valuation
      (encodeModelAtom first, encodeModelAtom value) := by
    exact hfirstValue.symm.trans hvalue
  by_contra hleaf
  obtain ⟨matched, fuel, hmatch⟩ :=
    exists_matchAtoms_of_solution_leaf ⟨valuation, hequation⟩ hleaf
  exact hne (matchAtoms_eq_of_nonvariable_leaf
    hfirstNonvar hvalueNonvar hleaf hmatch)

/-- Completeness of merging one semantically bounded right record into an
arbitrary satisfying live seed.  Only the right record is bounded: unrelated
payloads already present in the seed cannot participate in a conflict unless
they lie in the class of a bounded right-hand key. -/
def HESatisfiedMergeRelCompleteBelow
    (valuation : String → Metta.Atom) (bound : Nat) : Prop :=
  ∀ {seed right : Bindings},
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEBindingSatisfied valuation right →
    HEAssignmentsNonVariable right →
    HEBindingSolutionSizeBound valuation right bound →
    ∃ out, MergeRel seed right out ∧
      HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out

private theorem matchRel_satisfied_of_equation
    {valuation : String → Metta.Atom} {left right : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel left right out)
    (hequation : HEAtomEquationSatisfied valuation left right) :
    HEBindingSatisfied valuation out := by
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hmatch
  apply (matchAtoms_solution_iff hmem valuation).mpr
  simpa [HEAtomEquationSatisfied, MettaEquationSatisfied] using hequation

/-- Bounded matcher/list-matcher completeness, assuming only bounded merge
completeness at the same ceiling.  The simultaneous structural recursion is
the exact shape of `MatchRel.expr` and `MatchListAccRel.cons`: every child is
matched from empty and merged separately into the live accumulator. -/
private theorem boundedMatcherPack
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound) :
    (∀ {left right : Atom},
      HEAtomEquationSatisfied valuation left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, DeclMatchSpec.MatchRel left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound) ∧
    (∀ {lefts rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (encodeModelAtoms lefts) (encodeModelAtoms rights) →
      HESolutionAtomsSizeBound valuation lefts bound →
      HESolutionAtomsSizeBound valuation rights bound →
      ∃ out, DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound) := by
  let AtomGoal : Atom → Prop := fun left =>
    ∀ {right : Atom},
      HEAtomEquationSatisfied valuation left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, DeclMatchSpec.MatchRel left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound
  let ListGoal : List Atom → Prop := fun lefts =>
    ∀ {rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (encodeModelAtoms lefts) (encodeModelAtoms rights) →
      HESolutionAtomsSizeBound valuation lefts bound →
      HESolutionAtomsSizeBound valuation rights bound →
      ∃ out, DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound
  have leaf : ∀ {left right : Atom},
      HEAtomEquationSatisfied valuation left right →
      ¬ BothExpressions left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, DeclMatchSpec.MatchRel left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound := by
    intro left right hequation hleaf hleft hright
    obtain ⟨out, hmatch⟩ :=
      exists_matchRel_of_solution_leaf ⟨valuation, hequation⟩ hleaf
    exact ⟨out, hmatch,
      matchRel_satisfied_of_equation hmatch hequation,
      heAssignmentsNonVariable_of_matchRel hmatch,
      matchRel_solutionSizeBound hmatch hleft hright⟩
  have hrec : ∀ left, AtomGoal left := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol right hequation hleft hright
      exact leaf hequation (by simp [BothExpressions]) hleft hright
    · intro name right hequation hleft hright
      exact leaf hequation (by simp [BothExpressions]) hleft hright
    · intro ground right hequation hleft hright
      exact leaf hequation (by simp [BothExpressions]) hleft hright
    · intro lefts hlefts right hequation hleft hright
      cases right with
      | symbol symbol =>
          exact leaf hequation (by simp [BothExpressions]) hleft hright
      | var name =>
          exact leaf hequation (by simp [BothExpressions]) hleft hright
      | grounded ground =>
          exact leaf hequation (by simp [BothExpressions]) hleft hright
      | expression rights =>
          have hlists : MettaAtomListsSatisfied valuation
              (encodeModelAtoms lefts) (encodeModelAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              encodeModelAtom, applyClassSolution] using hequation
          obtain ⟨out, hlist, houtSat, houtNonvar, houtBound⟩ :=
            hlefts (seed := Bindings.empty)
              ((hesat_empty_iff valuation).mpr trivial)
              (by simp [HEAssignmentsNonVariable, Bindings.empty])
              (heBindingSolutionSizeBound_empty valuation bound)
              hlists
              (heSolutionAtomsSizeBound_of_expression_lt valuation hleft)
              (heSolutionAtomsSizeBound_of_expression_lt valuation hright)
          exact ⟨out, .expr hlist
      (heSemanticLoopFree_of_satisfied_nonvariable houtSat
        (fun {key target} => houtNonvar key target)),
      houtSat, houtNonvar, houtBound⟩
    · intro rights seed hseed hseedNonvar hseedBound hlists
        hleftsBound hrightsBound
      cases rights with
      | nil =>
          exact ⟨seed, .nil, hseed, hseedNonvar, hseedBound⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, encodeModelAtoms] at hlists
    · intro left lefts hleft hlefts rights seed hseed hseedNonvar
        hseedBound hlists hleftsBound hrightsBound
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, encodeModelAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
                MettaAtomListsSatisfied valuation
                  (encodeModelAtoms lefts) (encodeModelAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              encodeModelAtoms] using hlists
          obtain ⟨matched, hmatched, hmatchedSat, hmatchedNonvar,
              hmatchedBound⟩ :=
            hleft hequations.1 hleftsBound.head hrightsBound.head
          obtain ⟨next, hmergeRel, hnextSat, hnextNonvar⟩ :=
            hmerge hseed hseedNonvar hmatchedSat hmatchedNonvar
              hmatchedBound
          obtain ⟨mergeFuel, hmergeMem⟩ :=
            mergeBindings_complete hmergeRel
          have hnextBound :
              HEBindingSolutionSizeBound valuation next bound :=
            mergeRel_solutionSizeBound hmergeRel hseedBound hmatchedBound
          obtain ⟨out, htail, houtSat, houtNonvar, houtBound⟩ :=
            hlefts hnextSat hnextNonvar hnextBound hequations.2
              hleftsBound.tail hrightsBound.tail
          exact ⟨out, .cons hmatched hmergeMem htail,
            houtSat, houtNonvar, houtBound⟩
  refine ⟨?_, ?_⟩
  · intro left right hequation hleft hright
    exact hrec left hequation hleft hright
  · intro lefts rights seed hseed hseedNonvar hseedBound hlists
      hleftsBound hrightsBound
    induction lefts generalizing rights seed with
    | nil =>
        cases rights with
        | nil => exact ⟨seed, .nil, hseed, hseedNonvar, hseedBound⟩
        | cons right rights =>
            simp [MettaAtomListsSatisfied, encodeModelAtoms] at hlists
    | cons left lefts ih =>
        cases rights with
        | nil =>
            simp [MettaAtomListsSatisfied, encodeModelAtoms] at hlists
        | cons right rights =>
            have hequations :
                HEAtomEquationSatisfied valuation left right ∧
                  MettaAtomListsSatisfied valuation
                    (encodeModelAtoms lefts) (encodeModelAtoms rights) := by
              simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
                encodeModelAtoms] using hlists
            obtain ⟨matched, hmatched, hmatchedSat, hmatchedNonvar,
                hmatchedBound⟩ :=
              hrec left hequations.1 hleftsBound.head hrightsBound.head
            obtain ⟨next, hmergeRel, hnextSat, hnextNonvar⟩ :=
              hmerge hseed hseedNonvar hmatchedSat hmatchedNonvar
                hmatchedBound
            obtain ⟨mergeFuel, hmergeMem⟩ :=
              mergeBindings_complete hmergeRel
            have hnextBound :
                HEBindingSolutionSizeBound valuation next bound :=
              mergeRel_solutionSizeBound hmergeRel hseedBound hmatchedBound
            obtain ⟨out, htail, houtSat, houtNonvar, houtBound⟩ :=
              ih (rights := rights) (seed := next) hnextSat hnextNonvar
                hnextBound hequations.2 hleftsBound.tail hrightsBound.tail
            exact ⟨out, .cons hmatched hmergeMem htail,
              houtSat, houtNonvar, houtBound⟩

/-- Expression-root specialization.  The root itself may sit exactly at the
ceiling; every child is strictly smaller, so the produced binding record is
strictly bounded by the semantic size of the interpreted expression. -/
theorem exists_expressionMatchRel_solutionSizeBound
    {valuation : String → Metta.Atom} {lefts rights : List Atom}
    {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound)
    (hequation : HEAtomEquationSatisfied valuation
      (.expression lefts) (.expression rights))
    (hleftSize : HESolutionAtomSize valuation (.expression lefts) = bound)
    (hrightSize : HESolutionAtomSize valuation (.expression rights) = bound) :
    ∃ out, DeclMatchSpec.MatchRel (.expression lefts) (.expression rights) out ∧
      HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
          HEBindingSolutionSizeBound valuation out bound := by
  have hlists : MettaAtomListsSatisfied valuation
      (encodeModelAtoms lefts) (encodeModelAtoms rights) := by
    simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
      encodeModelAtom, applyClassSolution] using hequation
  have hleftBound : HESolutionAtomsSizeBound valuation lefts bound := by
    intro atom hmem
    rw [← hleftSize]
    exact heSolutionAtomSize_lt_expression_of_mem valuation hmem
  have hrightBound : HESolutionAtomsSizeBound valuation rights bound := by
    intro atom hmem
    rw [← hrightSize]
    exact heSolutionAtomSize_lt_expression_of_mem valuation hmem
  obtain ⟨out, hlist, houtSat, houtNonvar, houtBound⟩ :=
    (boundedMatcherPack hmerge).2
      ((hesat_empty_iff valuation).mpr trivial)
      (by simp [HEAssignmentsNonVariable, Bindings.empty])
      (heBindingSolutionSizeBound_empty valuation bound)
      hlists hleftBound hrightBound
  exact ⟨out, .expr hlist
      (heSemanticLoopFree_of_satisfied_nonvariable houtSat
        (fun {key target} => houtNonvar key target)),
      houtSat, houtNonvar, houtBound⟩

private theorem addVarBindingRel_satisfied
    {valuation : String → Metta.Atom} {seed out : Bindings}
    {key : String} {value : Atom}
    (hadd : AddVarBindingRel seed key value out)
    (hseed : HEBindingSatisfied valuation seed)
    (hvalue : valuation key =
      applyClassSolution valuation (encodeModelAtom value)) :
    HEBindingSatisfied valuation out := by
  obtain ⟨fuel, hmem⟩ := addVarBinding_complete hadd
  exact (addVarBinding_solution_iff hmem valuation).mpr ⟨hseed, hvalue⟩

private theorem addVarEqualityRel_satisfied
    {valuation : String → Metta.Atom} {seed out : Bindings}
    {left right : String}
    (hadd : AddVarEqualityRel seed left right out)
    (hseed : HEBindingSatisfied valuation seed)
    (hequality : valuation left = valuation right) :
    HEBindingSatisfied valuation out := by
  obtain ⟨fuel, hmem⟩ := addVarEquality_complete hadd
  exact (addVarEquality_solution_iff hmem valuation).mpr
    ⟨hseed, hequality⟩

/-- A co-satisfied pair of non-variable atoms at one semantic size either is
a reflexive leaf match or is an expression match whose bindings lie strictly
below that size. -/
private theorem exists_nonvariableMatchRel_at_solutionSize
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound)
    {left right : Atom}
    (hequation : HEAtomEquationSatisfied valuation left right)
    (hleftNonvar : DeclMatchSpec.Atom.isVarB left = false)
    (hrightNonvar : DeclMatchSpec.Atom.isVarB right = false)
    (hleftSize : HESolutionAtomSize valuation left = bound)
    (hrightSize : HESolutionAtomSize valuation right = bound) :
    ∃ out, DeclMatchSpec.MatchRel left right out ∧
      HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
          HEBindingSolutionSizeBound valuation out bound := by
  by_cases hexpressions : BothExpressions left right
  · rcases hexpressions with ⟨lefts, rights, rfl, rfl⟩
    exact exists_expressionMatchRel_solutionSizeBound hmerge hequation
      hleftSize hrightSize
  · obtain ⟨out, hmatch⟩ :=
      exists_matchRel_of_solution_leaf ⟨valuation, hequation⟩ hexpressions
    have houtBound :
        HEBindingSolutionSizeBound valuation out bound := by
      cases hmatch with
      | symSym => exact heBindingSolutionSizeBound_empty valuation bound
      | varVar => simp [DeclMatchSpec.Atom.isVarB] at hleftNonvar
      | varNonVar => simp [DeclMatchSpec.Atom.isVarB] at hleftNonvar
      | nonVarVar => simp [DeclMatchSpec.Atom.isVarB] at hrightNonvar
      | grounded => exact heBindingSolutionSizeBound_empty valuation bound
      | expr => exact (hexpressions (by simp [BothExpressions])).elim
    exact ⟨out, hmatch,
      matchRel_satisfied_of_equation hmatch hequation,
      heAssignmentsNonVariable_of_matchRel hmatch,
      houtBound⟩

/-- Pointwise reconciliation for class values at one semantic size.  Equal
leaf pairs contribute no bindings; expression pairs contribute only strict
semantic subterms.  Each resulting child record is merged into the live
accumulator through the same bounded merge hypothesis. -/
private theorem exists_nonvariableMatchListAccRel_at_solutionSize
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound) :
    ∀ {lefts rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (encodeModelAtoms lefts) (encodeModelAtoms rights) →
      (∀ atom ∈ lefts,
        DeclMatchSpec.Atom.isVarB atom = false ∧
          HESolutionAtomSize valuation atom = bound) →
      (∀ atom ∈ rights,
        DeclMatchSpec.Atom.isVarB atom = false ∧
          HESolutionAtomSize valuation atom = bound) →
      ∃ out, DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound := by
  intro lefts
  induction lefts with
  | nil =>
      intro rights seed hseed hseedNonvar hseedBound hlists _ _
      cases rights with
      | nil => exact ⟨seed, .nil, hseed, hseedNonvar, hseedBound⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, encodeModelAtoms] at hlists
  | cons left lefts ih =>
      intro rights seed hseed hseedNonvar hseedBound hlists hlefts hrights
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, encodeModelAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
                MettaAtomListsSatisfied valuation
                  (encodeModelAtoms lefts) (encodeModelAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              encodeModelAtoms] using hlists
          have hleft := hlefts left (by simp)
          have hright := hrights right (by simp)
          obtain ⟨matched, hmatched, hmatchedSat, hmatchedNonvar,
              hmatchedBound⟩ :=
            exists_nonvariableMatchRel_at_solutionSize hmerge
              hequations.1 hleft.1 hright.1 hleft.2 hright.2
          obtain ⟨next, hmergeRel, hnextSat, hnextNonvar⟩ :=
            hmerge hseed hseedNonvar hmatchedSat hmatchedNonvar
              hmatchedBound
          obtain ⟨mergeFuel, hmergeMem⟩ :=
            mergeBindings_complete hmergeRel
          have hnextBound :
              HEBindingSolutionSizeBound valuation next bound :=
            mergeRel_solutionSizeBound hmergeRel hseedBound hmatchedBound
          have hleftTail : ∀ atom ∈ lefts,
              DeclMatchSpec.Atom.isVarB atom = false ∧
                HESolutionAtomSize valuation atom = bound := by
            intro atom hmem
            exact hlefts atom (by simp [hmem])
          have hrightTail : ∀ atom ∈ rights,
              DeclMatchSpec.Atom.isVarB atom = false ∧
                HESolutionAtomSize valuation atom = bound := by
            intro atom hmem
            exact hrights atom (by simp [hmem])
          obtain ⟨out, htail, houtSat, houtNonvar, houtBound⟩ :=
            ih hnextSat hnextNonvar hnextBound hequations.2
              hleftTail hrightTail
          exact ⟨out, .cons hmatched hmergeMem htail,
            houtSat, houtNonvar, houtBound⟩

/-- Fold bounded value/equality insertion callbacks into the exact
assignment-then-equality `MergeRel` prescribed by HE. -/
private theorem satisfiedMergeRelCompleteBelow_of_adds
    {valuation : String → Metta.Atom} {bound : Nat}
    (haddValue : ∀ {seed : Bindings} {key : String} {value : Atom},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      DeclMatchSpec.Atom.isVarB value = false →
      valuation key = applyClassSolution valuation (encodeModelAtom value) →
      (valuation key).size < bound →
      HESolutionAtomSize valuation value < bound →
      ∃ out, AddVarBindingRel seed key value out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out)
    (haddEquality : ∀ {seed : Bindings} {left right : String},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      valuation left = valuation right →
      (valuation left).size < bound →
      (valuation right).size < bound →
      ∃ out, AddVarEqualityRel seed left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out) :
    HESatisfiedMergeRelCompleteBelow valuation bound := by
  intro seed right hseed hseedNonvar hright hrightNonvar hrightBound
  have foldAssignments : ∀
      (assignments : List (String × Atom)) (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      (∀ key value, (key, value) ∈ assignments →
        valuation key =
          applyClassSolution valuation (encodeModelAtom value)) →
      (∀ key value, (key, value) ∈ assignments →
        DeclMatchSpec.Atom.isVarB value = false) →
      (∀ key value, (key, value) ∈ assignments →
        (valuation key).size < bound ∧
          HESolutionAtomSize valuation value < bound) →
      ∃ after, MergeAssignsRel before assignments after ∧
        HEBindingSatisfied valuation after ∧
          HEAssignmentsNonVariable after := by
    intro assignments
    induction assignments with
    | nil =>
        intro before hbefore hnonvar _ _ _
        exact ⟨before, .nil, hbefore, hnonvar⟩
    | cons assignment rest ih =>
        rcases assignment with ⟨key, value⟩
        intro before hbefore hnonvar hsat hvalues hbounds
        obtain ⟨next, hadd, hnextSat, hnextNonvar⟩ :=
          haddValue hbefore hnonvar
            (hvalues key value (by simp))
            (hsat key value (by simp))
            (hbounds key value (by simp)).1
            (hbounds key value (by simp)).2
        have hrestSat : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            valuation restKey = applyClassSolution valuation
              (encodeModelAtom restValue) := by
          intro restKey restValue hmem
          exact hsat restKey restValue (by simp [hmem])
        have hrestValues : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            DeclMatchSpec.Atom.isVarB restValue = false := by
          intro restKey restValue hmem
          exact hvalues restKey restValue (by simp [hmem])
        have hrestBounds : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            (valuation restKey).size < bound ∧
              HESolutionAtomSize valuation restValue < bound := by
          intro restKey restValue hmem
          exact hbounds restKey restValue (by simp [hmem])
        obtain ⟨after, htail, hafterSat, hafterNonvar⟩ :=
          ih next hnextSat hnextNonvar hrestSat hrestValues hrestBounds
        exact ⟨after, .cons hadd htail, hafterSat, hafterNonvar⟩
  have foldEqualities : ∀
      (equalities : List (String × String)) (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      (∀ left right, (left, right) ∈ equalities →
        valuation left = valuation right) →
      (∀ left right, (left, right) ∈ equalities →
        (valuation left).size < bound ∧
          (valuation right).size < bound) →
      ∃ after, MergeEqsRel before equalities after ∧
        HEBindingSatisfied valuation after ∧
          HEAssignmentsNonVariable after := by
    intro equalities
    induction equalities with
    | nil =>
        intro before hbefore hnonvar _ _
        exact ⟨before, .nil, hbefore, hnonvar⟩
    | cons equality rest ih =>
        rcases equality with ⟨left, right⟩
        intro before hbefore hnonvar hsat hbounds
        obtain ⟨next, hadd, hnextSat, hnextNonvar⟩ :=
          haddEquality hbefore hnonvar
            (hsat left right (by simp))
            (hbounds left right (by simp)).1
            (hbounds left right (by simp)).2
        have hrestSat : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            valuation restLeft = valuation restRight := by
          intro restLeft restRight hmem
          exact hsat restLeft restRight (by simp [hmem])
        have hrestBounds : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            (valuation restLeft).size < bound ∧
              (valuation restRight).size < bound := by
          intro restLeft restRight hmem
          exact hbounds restLeft restRight (by simp [hmem])
        obtain ⟨after, htail, hafterSat, hafterNonvar⟩ :=
          ih next hnextSat hnextNonvar hrestSat hrestBounds
        exact ⟨after, .cons hadd htail, hafterSat, hafterNonvar⟩
  obtain ⟨middle, hassignments, hmiddleSat, hmiddleNonvar⟩ :=
    foldAssignments right.assignments seed hseed hseedNonvar
      (fun key value hmem => hright.1 key value hmem)
      (fun key value hmem =>
        hrightNonvar.isVarB_eq_false_of_assignment hmem)
      (fun key value hmem => hrightBound.1 key value hmem)
  obtain ⟨out, hequalities, houtSat, houtNonvar⟩ :=
    foldEqualities right.equalities middle hmiddleSat hmiddleNonvar
      (fun left right hmem => hright.2 left right hmem)
      (fun left right hmem => hrightBound.2 left right hmem)
  exact ⟨out, .mk hassignments hequalities, houtSat, houtNonvar⟩

/-- The operational keystone.  Strong induction is on the semantic ceiling of
the right record.  A value/equality insertion at key size `k < bound` invokes
the original HE matcher at size `k`; expression matching emits only bindings
strictly below `k`, so its live merge is supplied by the induction hypothesis
at `k`.  The seed is never measured. -/
theorem satisfiedMergeRelCompleteBelow
    (valuation : String → Metta.Atom) :
    ∀ bound, HESatisfiedMergeRelCompleteBelow valuation bound := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
      apply satisfiedMergeRelCompleteBelow_of_adds
      · intro seed key value hseed hseedNonvar hvalueNonvar hvalue
          hkeyBound hvalueBound
        cases hclass : seed.classValues key with
        | nil =>
            let hadd : AddVarBindingRel seed key value
                (seed.assign key value) := .fresh hclass
            exact ⟨seed.assign key value, hadd,
              addVarBindingRel_satisfied hadd hseed hvalue,
              hseedNonvar.assign hvalueNonvar⟩
        | cons first rest =>
            cases hconsistent :
                Bindings.valuesConsistent (first :: rest) with
            | true =>
                by_cases hequal : first = value
                · let hadd : AddVarBindingRel seed key value seed :=
                    .same hclass hconsistent hequal
                  exact ⟨seed, hadd,
                    addVarBindingRel_satisfied hadd hseed hvalue,
                    hseedNonvar⟩
                · have hfirstMem : first ∈ seed.classValues key := by
                    rw [hclass]
                    exact List.mem_cons_self ..
                  have hfirstEquation : HEAtomEquationSatisfied valuation
                      first value :=
                    (hseed.eq_applyClassSolution_of_mem_classValues
                      hfirstMem).symm.trans hvalue
                  have hfirstSize : HESolutionAtomSize valuation first =
                      (valuation key).size :=
                    hseed.solutionAtomSize_classValue hfirstMem
                  have hvalueSize : HESolutionAtomSize valuation value =
                      (valuation key).size := by
                    exact congrArg Metta.Atom.size hvalue.symm
                  obtain ⟨lefts, rights, hfirstExpr, hvalueExpr⟩ :=
                    bothExpressions_of_ne_classValue_coSatisfied
                      hseed hseedNonvar hclass hvalueNonvar hvalue hequal
                  subst first
                  subst value
                  obtain ⟨matched, hmatch, hmatchedSat, hmatchedNonvar,
                      hmatchedBound⟩ :=
                    exists_expressionMatchRel_solutionSizeBound
                      (ih _ hkeyBound) hfirstEquation hfirstSize hvalueSize
                  obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                    ih _ hkeyBound hseed hseedNonvar hmatchedSat
                      hmatchedNonvar hmatchedBound
                  let hadd : AddVarBindingRel seed key
                      (.expression rights) out :=
                    .conflict hclass hconsistent hequal hmatch hmerge
                  exact ⟨out, hadd,
                    addVarBindingRel_satisfied hadd hseed hvalue,
                    houtNonvar⟩
            | false =>
                have hfirstMem : first ∈ seed.classValues key := by
                  rw [hclass]
                  exact List.mem_cons_self ..
                have hfirstSize : HESolutionAtomSize valuation first =
                    (valuation key).size :=
                  hseed.solutionAtomSize_classValue hfirstMem
                have hvalueSize : HESolutionAtomSize valuation value =
                    (valuation key).size := by
                  exact congrArg Metta.Atom.size hvalue.symm
                have hfirstNonvar :
                    DeclMatchSpec.Atom.isVarB first = false :=
                  hseedNonvar.isVarB_eq_false_of_classValue hfirstMem
                have hlists := classValues_reconcileList_satisfied
                  hseed hclass hvalue
                have hleftData : ∀ atom ∈
                    List.replicate (rest.length + 1) first,
                    DeclMatchSpec.Atom.isVarB atom = false ∧
                      HESolutionAtomSize valuation atom =
                        (valuation key).size := by
                  intro atom hmem
                  have hatom : atom = first := List.eq_of_mem_replicate hmem
                  subst atom
                  exact ⟨hfirstNonvar, hfirstSize⟩
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
                      hseedNonvar.isVarB_eq_false_of_classValue hclassMem,
                      hseed.solutionAtomSize_classValue hclassMem⟩
                  · simp only [List.mem_singleton] at hlast
                    subst atom
                    exact ⟨hvalueNonvar, hvalueSize⟩
                obtain ⟨matched, hmatch, hmatchedSat, hmatchedNonvar,
                    hmatchedBound⟩ :=
                  exists_nonvariableMatchListAccRel_at_solutionSize
                    (ih _ hkeyBound)
                    ((hesat_empty_iff valuation).mpr trivial)
                    (by simp [HEAssignmentsNonVariable, Bindings.empty])
                    (heBindingSolutionSizeBound_empty valuation
                      (valuation key).size)
                    hlists hleftData hrightData
                obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                  ih _ hkeyBound hseed hseedNonvar hmatchedSat
                    hmatchedNonvar hmatchedBound
                let hadd : AddVarBindingRel seed key value out :=
                  .reconcile hclass hconsistent hmatch hmerge
                exact ⟨out, hadd,
                  addVarBindingRel_satisfied hadd hseed hvalue,
                  houtNonvar⟩
      · intro seed left right hseed hseedNonvar hequality hleftBound
          hrightBound
        have hcandidateSat : HEBindingSatisfied valuation
            (seed.addEquality left right) :=
          (hesat_addEquality (b := seed) (a := left) (c := right) valuation).mpr
            ⟨hseed, hequality⟩
        have hcandidateNonvar :
            HEAssignmentsNonVariable (seed.addEquality left right) :=
          hseedNonvar.addEquality left right
        cases hconsistent : Bindings.valuesConsistent
            ((seed.addEquality left right).classValues left) with
        | true =>
            let hadd : AddVarEqualityRel seed left right
                (seed.addEquality left right) := .consistent hconsistent
            exact ⟨seed.addEquality left right, hadd,
              addVarEqualityRel_satisfied hadd hseed hequality,
              hcandidateNonvar⟩
        | false =>
            cases hvalues :
                (seed.addEquality left right).classValues left with
            | nil =>
                rw [hvalues] at hconsistent
                simp [Bindings.valuesConsistent] at hconsistent
            | cons first rest =>
                cases rest with
                | nil =>
                    rw [hvalues] at hconsistent
                    simp [Bindings.valuesConsistent] at hconsistent
                | cons second tail =>
                    cases tail with
                    | nil =>
                        have hfirstMem : first ∈
                            (seed.addEquality left right).classValues left := by
                          rw [hvalues]
                          simp
                        have hsecondMem : second ∈
                            (seed.addEquality left right).classValues left := by
                          rw [hvalues]
                          simp
                        have hequation : HEAtomEquationSatisfied valuation
                            first second :=
                          classValues_equationSatisfied hcandidateSat
                            hfirstMem hsecondMem
                        have hfirstSize :
                            HESolutionAtomSize valuation first =
                              (valuation left).size :=
                          hcandidateSat.solutionAtomSize_classValue hfirstMem
                        have hsecondSize :
                            HESolutionAtomSize valuation second =
                              (valuation left).size :=
                          hcandidateSat.solutionAtomSize_classValue hsecondMem
                        obtain ⟨matched, hmatch, hmatchedSat,
                            hmatchedNonvar, hmatchedBound⟩ :=
                          exists_nonvariableMatchRel_at_solutionSize
                            (ih _ hleftBound) hequation
                            (hcandidateNonvar.isVarB_eq_false_of_classValue
                              hfirstMem)
                            (hcandidateNonvar.isVarB_eq_false_of_classValue
                              hsecondMem)
                            hfirstSize hsecondSize
                        obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                          ih _ hleftBound hcandidateSat hcandidateNonvar
                            hmatchedSat hmatchedNonvar hmatchedBound
                        have hpairInconsistent :
                            Bindings.valuesConsistent [first, second] = false := by
                          simpa [hvalues] using hconsistent
                        let hadd : AddVarEqualityRel seed left right out :=
                          .pairConflict hvalues hpairInconsistent hmatch hmerge
                        exact ⟨out, hadd,
                          addVarEqualityRel_satisfied hadd hseed hequality,
                          houtNonvar⟩

                    | cons third rest =>
                        have hfirstMem : first ∈
                            (seed.addEquality left right).classValues left := by
                          rw [hvalues]
                          simp
                        have hfirstSize :
                            HESolutionAtomSize valuation first =
                              (valuation left).size :=
                          hcandidateSat.solutionAtomSize_classValue hfirstMem
                        have hfirstNonvar :
                            DeclMatchSpec.Atom.isVarB first = false :=
                          hcandidateNonvar.isVarB_eq_false_of_classValue
                            hfirstMem
                        have hlists : MettaAtomListsSatisfied valuation
                            (encodeModelAtoms
                              (List.replicate (rest.length + 2) first))
                            (encodeModelAtoms (second :: third :: rest)) := by
                          have h := classValues_replicateTail_satisfied
                            hcandidateSat hvalues
                          simpa using h
                        have hleftData : ∀ atom ∈
                            List.replicate (rest.length + 2) first,
                            DeclMatchSpec.Atom.isVarB atom = false ∧
                              HESolutionAtomSize valuation atom =
                                (valuation left).size := by
                          intro atom hmem
                          have hatom : atom = first :=
                            List.eq_of_mem_replicate hmem
                          subst atom
                          exact ⟨hfirstNonvar, hfirstSize⟩
                        have hrightData : ∀ atom ∈ second :: third :: rest,
                            DeclMatchSpec.Atom.isVarB atom = false ∧
                              HESolutionAtomSize valuation atom =
                                (valuation left).size := by
                          intro atom hmem
                          have hclassMem : atom ∈
                              (seed.addEquality left right).classValues left := by
                            rw [hvalues]
                            exact List.mem_cons_of_mem first hmem
                          exact ⟨
                            hcandidateNonvar.isVarB_eq_false_of_classValue
                              hclassMem,
                            hcandidateSat.solutionAtomSize_classValue
                              hclassMem⟩
                        obtain ⟨matched, hmatch, hmatchedSat,
                            hmatchedNonvar, hmatchedBound⟩ :=
                          exists_nonvariableMatchListAccRel_at_solutionSize
                            (ih _ hleftBound)
                            ((hesat_empty_iff valuation).mpr trivial)
                            (by
                              simp [HEAssignmentsNonVariable, Bindings.empty])
                            (heBindingSolutionSizeBound_empty valuation
                              (valuation left).size)
                            hlists hleftData hrightData
                        obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                          ih _ hleftBound hcandidateSat hcandidateNonvar
                            hmatchedSat hmatchedNonvar hmatchedBound
                        have hclassInconsistent : Bindings.valuesConsistent
                            (first :: second :: third :: rest) = false := by
                          simpa [hvalues] using hconsistent
                        let hadd : AddVarEqualityRel seed left right out :=
                          .classConflict hvalues hclassInconsistent hmatch hmerge
                        exact ⟨out, hadd,
                          addVarEqualityRel_satisfied hadd hseed hequality,
                          houtNonvar⟩

/-- Two finite, nonvariable-shaped records with a common model have an
actual finite-depth merge. The local size ceiling is constructed from the
right record; it is not a caller-supplied semantic restriction. -/
theorem exists_mergeBindings_of_common_model
    {left right : Bindings} {valuation : String → Metta.Atom}
    (leftModel : HEBindingSatisfied valuation left)
    (leftShape : HEAssignmentsNonVariable left)
    (rightModel : HEBindingSatisfied valuation right)
    (rightShape : HEAssignmentsNonVariable right) :
    ∃ output depth, output ∈ mergeBindings left right depth := by
  obtain ⟨bound,covered⟩ := exists_heBindingSolutionSizeBound valuation right
  obtain ⟨output,merged,_,_⟩ := satisfiedMergeRelCompleteBelow valuation bound
    leftModel leftShape rightModel rightShape covered
  obtain ⟨depth,occurred⟩ := DeclMergeSpec.mergeBindings_complete merged
  exact ⟨output,depth,occurred⟩

/-- Assumption-free semantic completeness of the declarative HE matcher.
The recursive expression/list proof is the existing representation-free
construction; semantic-size merge-back supplies its former local premise. -/
theorem exists_matchRel_of_solution_solutionSize
    {left right : Atom} {valuation : String → Metta.Atom}
    (hequation : HEAtomEquationSatisfied valuation left right) :
    ∃ out, DeclMatchSpec.MatchRel left right out := by
  let bound := max (HESolutionAtomSize valuation left) (HESolutionAtomSize valuation right) + 1
  obtain ⟨out,matched,_,_,_⟩ :=
    (boundedMatcherPack (satisfiedMergeRelCompleteBelow valuation bound)).1 hequation
      ((Nat.le_max_left _ _).trans_lt (Nat.lt_succ_self _))
      ((Nat.le_max_right _ _).trans_lt (Nat.lt_succ_self _))
  exact ⟨out,matched⟩

/-- Executable finite-fuel form of assumption-free semantic matcher
completeness. -/
theorem exists_matchAtoms_of_solution_solutionSize
    {left right : Atom} {valuation : String → Metta.Atom}
    (hequation : HEAtomEquationSatisfied valuation left right) :
    ∃ out fuel, out ∈ matchAtoms left right fuel := by
  obtain ⟨out,matched⟩ := exists_matchRel_of_solution_solutionSize hequation
  obtain ⟨depth,occurred⟩ := DeclMatchSpec.matchAtoms_complete matched
  exact ⟨out,depth,occurred⟩

/-- Completed matcher coverage earns a semantic witness at its actual
depth. Existence at some larger depth is transported back using the proved
stability law, rather than treating an empty bounded list as failure. -/
theorem covered_match_of_solution
    {left right : Atom} {valuation : String → Metta.Atom} {depth : Nat}
    (covered : matchCovered depth (.atoms left right) = true)
    (equation : HEAtomEquationSatisfied valuation left right) :
    ∃ output, output ∈ matchAtoms left right depth := by
  obtain ⟨output,witnessDepth,occurred⟩ := exists_matchAtoms_of_solution_solutionSize equation
  have later := DeclMatchSpec.matchAtoms_mono left right witnessDepth depth occurred
  have stable := matchCovered_stable depth witnessDepth (.atoms left right) covered
  change matchAtoms left right (depth + witnessDepth) = matchAtoms left right depth at stable
  rw [Nat.add_comm witnessDepth depth,stable] at later
  exact ⟨output,later⟩

end Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
