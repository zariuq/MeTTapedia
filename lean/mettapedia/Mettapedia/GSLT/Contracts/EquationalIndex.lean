import Mettapedia.Data.List.OrderedPrefilter
import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mettapedia.GSLT.Contracts.ACUReplacement

/-!
# A sound index coordinate for matching modulo equations

An index may reject a candidate only if its chosen key is forced by
every admissible instantiation of the query. An unproved coordinate
can be treated as a wildcard. An exact canonicalizer for equality is
necessary for full canonical-key matching, but it does not on its own
justify a rigid projection on an open pattern.

The indexed operation below preserves the ordered answer word, not
just the set of substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.EquationalIndex

open Mettapedia.Data.List.OrderedPrefilter (filter_flatMap_eq_iff)
open Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses (NormalForms)

universe u v w

variable {Term : Type u} {Assignment : Type v} {Key : Type w} [DecidableEq Key]

def accepts (feature : Term → Key) (restriction : Option Key) (row : Term) : Bool :=
  match restriction with
  | none => true
  | some fixed => decide (feature row = fixed)

def indexedAnswers (feature : Term → Key) (restriction : Option Key)
    (answers : Term → List Assignment) (rows : List Term) : List Assignment :=
  (rows.filter (accepts feature restriction)).flatMap answers

/-- The exact scope-independent licence for a rigid bucket. The
completeness direction tests the row consisting of an instance itself. -/
theorem rigid_exact_iff (equations : Setoid Term) (feature : Term → Key)
    (invariant : ∀ {first second}, equations.r first second → feature first = feature second)
    (instantiate : Assignment → Term) (admissible : Assignment → Prop)
    (answers : Term → List Assignment)
    (spec : ∀ row assignment, assignment ∈ answers row ↔
      admissible assignment ∧ equations.r (instantiate assignment) row)
    (fixed : Key) :
    (∀ rows, indexedAnswers feature (some fixed) answers rows = rows.flatMap answers) ↔
      ∀ assignment, admissible assignment → feature (instantiate assignment) = fixed := by
  constructor
  · intro exactAll assignment allowed
    have member : assignment ∈ answers (instantiate assignment) :=
      (spec _ _).mpr ⟨allowed, equations.iseqv.refl _⟩
    have coverage := (filter_flatMap_eq_iff (accepts feature (some fixed)) answers [_]).mp
      (exactAll [instantiate assignment])
    have notEmpty : answers (instantiate assignment) ≠ [] := by
      intro empty
      simp only [empty, List.not_mem_nil] at member
    simpa only [accepts, decide_eq_true_eq] using coverage _ (by simp) notEmpty
  · intro stable rows
    apply (filter_flatMap_eq_iff (accepts feature (some fixed)) answers rows).mpr
    intro row _ emits
    obtain ⟨assignment, member⟩ := List.exists_mem_of_ne_nil _ emits
    obtain ⟨allowed, agrees⟩ := (spec row assignment).mp member
    simp only [accepts, decide_eq_true_eq]
    exact (invariant agrees).symm.trans (stable assignment allowed)

theorem wildcard_exact (feature : Term → Key) (answers : Term → List Assignment) (rows : List Term) :
    indexedAnswers feature none answers rows = rows.flatMap answers :=
  (filter_flatMap_eq_iff (accepts feature none) answers rows).mpr (fun _ _ _ => rfl)

omit [DecidableEq Key] in
/-- Features may be derived from full canonical keys. This preserves the
class-invariance premise, not the separate instantiation premise. -/
theorem canonical_feature_invariant {equations : Setoid Term} (forms : NormalForms equations)
    (project : forms.Key → Key) {first second : Term} (agree : equations.r first second) :
    project (forms.key first) = project (forms.key second) :=
  congrArg project (forms.key_eq_iff.mpr agree)

namespace Controls

inductive Expr where
  | f (argument : Nat)
  | g (argument : Nat)
  deriving DecidableEq

/-- A regular, collapse-free ground axiom. Nat parameters have no
equations, so there are no further contexts at this result sort. -/
inductive GroundAxiom : Expr → Expr → Prop where
  | changeZero : GroundAxiom (.f 0) (.g 0)

def normalize : Expr → Expr
  | .f 0 => .g 0
  | term => term

theorem axiomClosure_iff_sameNormal (a b : Expr) :
    Relation.EqvGen GroundAxiom a b ↔ normalize a = normalize b := by
  constructor
  · intro same
    induction same with
    | rel _ _ step => cases step; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  · intro same
    have normalizes (term : Expr) : Relation.EqvGen GroundAxiom term (normalize term) := by
      cases term with
      | f n => cases n with
        | zero => exact .rel _ _ .changeZero
        | succ _ => exact .refl _
      | g _ => exact .refl _
    exact .trans _ _ _ (normalizes a) (.symm _ _ (same.symm ▸ normalizes b))

private def head (term : Expr) : Bool :=
  match normalize term with
  | .f _ => false
  | .g _ => true

private def solveZero (term : Expr) : List Nat :=
  if normalize term = normalize (.f 0) then [0] else []

/-- The head of f(x) is not a safe bucket even though the declaration
does not collapse a term to a variable: grounding x can change it. -/
theorem collapse_free_still_needs_stability :
    Relation.EqvGen GroundAxiom (.f 0) (.g 0) ∧
      indexedAnswers head (some false) solveZero [.g 0] = [] ∧
      indexedAnswers head none solveZero [.g 0] = [0] ∧
      indexedAnswers head (some true) solveZero [.f 0, .g 0] = [0, 0] :=
  ⟨.rel _ _ .changeZero, by decide, by decide, by decide⟩

open ACUReplacement in
/-- The unit law can erase an operator entirely; it is not just a
change of bucket between two rigid constructors. -/
theorem unit_erases_open_head :
    Equation (.op (.atom (2 : Nat)) .unit) (.atom 2) ∧
      let headTag : ACUReplacement.Term Nat → Bool := fun term => match term with
        | .op .. => true
        | _ => false
      accepts headTag (some true) (.atom 2) = false :=
  ⟨.rightUnit _, rfl⟩

end Controls

#print axioms rigid_exact_iff
#print axioms wildcard_exact
#print axioms Controls.axiomClosure_iff_sameNormal
#print axioms Controls.collapse_free_still_needs_stability
#print axioms Controls.unit_erases_open_head

end Mettapedia.GSLT.Contracts.EquationalIndex
