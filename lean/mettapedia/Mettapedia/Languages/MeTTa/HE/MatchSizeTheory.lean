import Mettapedia.Languages.MeTTa.HE.MatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.DeclMergeSpec

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
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Structural size of an HE atom, measured after the faithful LeaTTa
translation used by the equation lane. -/
def HEAtomSize (atom : Atom) : Nat :=
  (toLeaTTaAtom atom).size

/-- Structural size after interpreting variables through a common solution.
Unlike raw syntax size, this measure sees a live class value as the semantic
subterm occupying its variable position. -/
def HESolutionAtomSize (valuation : String → Metta.Atom)
    (atom : Atom) : Nat :=
  (applyClassSolution valuation (toLeaTTaAtom atom)).size

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
  simp [HESolutionAtomSize, toLeaTTaAtom, applyClassSolution]

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

private theorem toLeaTTaAtoms_eq_map (atoms : List Atom) :
    toLeaTTaAtoms atoms = atoms.map toLeaTTaAtom := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih => simp [toLeaTTaAtoms, ih]

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
  rw [toLeaTTaAtoms_eq_map]
  exact List.mem_map.mpr ⟨atom, hmem, rfl⟩

/-- Interpreting variables preserves the strict child-of-expression size
descent.  This is the semantic measure needed when a live seed expands a
variable to a raw term as large as its enclosing syntax. -/
theorem heSolutionAtomSize_lt_expression_of_mem
    (valuation : String → Metta.Atom) {atom : Atom} {atoms : List Atom}
    (hmem : atom ∈ atoms) :
    HESolutionAtomSize valuation atom <
      HESolutionAtomSize valuation (.expression atoms) := by
  have htranslated : toLeaTTaAtom atom ∈ toLeaTTaAtoms atoms := by
    rw [toLeaTTaAtoms_eq_map]
    exact List.mem_map.mpr ⟨atom, hmem, rfl⟩
  have happly : applyClassSolution valuation (toLeaTTaAtom atom) ∈
      (toLeaTTaAtoms atoms).map (applyClassSolution valuation) :=
    List.mem_map.mpr ⟨toLeaTTaAtom atom, htranslated, rfl⟩
  have hstrict := mettaAtom_size_lt_expr_of_mem happly
  simpa [HESolutionAtomSize, toLeaTTaAtom, applyClassSolution] using hstrict

theorem heSolutionAtomsSizeBound_of_expression_lt
    (valuation : String → Metta.Atom) {atoms : List Atom} {bound : Nat}
    (h : HESolutionAtomSize valuation (.expression atoms) < bound) :
    HESolutionAtomsSizeBound valuation atoms bound := by
  intro atom hmem
  exact (heSolutionAtomSize_lt_expression_of_mem valuation hmem).trans h

/-- A satisfied live class value has exactly the semantic size of the
variable whose class exposes it. -/
theorem HEBindingSatisfied.solutionAtomSize_classValue
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

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
