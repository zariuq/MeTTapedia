import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalUnification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelHenkin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalCheckRegions

/-!
# The rational-tree check calculus and its free model

This mirrors `ModelDerivation` for the rational-tree fibre. The two calculi are siblings, each sound
for its own algebra: the finite one refutes by the occurs-checked unifier and is sound for finite
terms; this one refutes by clashes only and is sound for rational trees. A refutation of one is not
a refutation of the other (control in `RationalControls`).

* **Syntax**: the checks (equality, absence, count) of a store of rational trees, read as guard
  formulas by `checkGuard`.
* **Derivability** (`RationalChecks.Derives`): three rules over the solved form `mgu` of the store,
  each requiring that the solved form solves the store:
  - `equal`: the solved form identifies both sides;
  - `absent`: each occurrence of the region is refuted by a clash with the pattern;
  - `count`: the solved form matches exactly `number` occurrences, and each other occurrence is
    refuted by a clash.
* **Model**: the algebra of rational trees (`treeModel`), with rational substitutions as its points.
  It is free (`treeModel_free`).

**Soundness and completeness** (`derives_iff_entails`, `derives_iff_treeModel`): a check is derivable
exactly when the store is solvable over rational trees and the check holds at every solution, which
is validity in the rational tree algebra.

**Consistency** (`not_derives_clash`): for distinct constants, `c = d` is derivable from no store.
It follows from the model: a derivation would make `c = d` hold at a point of the tree algebra.

The calculus reads the classical solved form; it is a proof logic with semantic premises. Its
consistency premise is decidable on finite presentations (`RationalDecision`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP
open Interface (Frames GuardFormula)
open AnnotatedRuns (checkGuard checkGuard_sat)

variable (σ : LPSignature)

/-- **The rational tree algebra as a Henkin model of the rational-tree frames**: its values are
rational trees, its points rational substitutions, and evaluation is substitution. -/
def treeModel : (rationalFrames σ).HenkinModel (RTree σ) (fun _ => RSubst σ) where
  eval t ρ := RTree.subst ρ t
  pull θ ρ := (rationalAction σ).compose ρ θ
  eval_act θ t ρ := (RTree.subst_comp ρ θ t).symm
  eval_E same ρ := congrArg (RTree.subst ρ) same

variable {σ}

theorem treeModel_realizes (θ : RSubst σ) :
    (treeModel σ).Realizes (a := PUnit.unit) (b := PUnit.unit) θ θ := fun _ _ => Iff.rfl

/-- **The rational tree algebra is a free model.** -/
theorem treeModel_free : (treeModel σ).Free := fun _ θ => ⟨PUnit.unit, θ, treeModel_realizes θ⟩

/-- **Asks over rational trees are validity in the rational tree algebra.** -/
theorem entails_iff_treeModel {O : Type*} (store : EquationStore (RTree σ))
    (φ : GuardFormula (RTree σ) O) :
    (rationalFrames σ).Entails (a := PUnit.unit) store
        (fun b θ => (rationalFrames σ).Satisfies (a := PUnit.unit) (b := b) θ φ) ↔
      ∀ ρ : RSubst σ, (treeModel σ).Models (a := PUnit.unit) ρ store →
        (treeModel σ).Satisfies (a := PUnit.unit) ρ φ := by
  constructor
  · exact fun asked ρ known => Frames.HenkinModel.sound treeModel_free asked ρ known
  · intro valid _ θ solved
    exact (Frames.HenkinModel.satisfies_iff_of_realizes (treeModel_realizes θ) φ).mp
      (valid θ ((Frames.HenkinModel.models_iff_of_realizes (treeModel_realizes θ) store).mpr solved))

/-- The solved form solves exactly the solvable stores. -/
theorem models_mgu_iff (store : EquationStore (RTree σ)) :
    (rationalAction σ).Models (mgu store) store ↔ (rationalAction σ).Consistent store :=
  ⟨fun solved => ⟨_, solved⟩, fun consistent =>
    (mgu_principal ((consistent_iff_not_refuted store).mp consistent)).sound⟩

namespace RationalChecks

variable {O : Type}

/-- The occurrences the solved form matches with a pattern. -/
noncomputable def certain (problem : EquationStore (RTree σ)) (label : O → RTree σ) (world : Finset O)
    (pattern : RTree σ) : Finset O :=
  Check.matches (rationalAction σ) (mgu problem) label world pattern

/-- **The rational-tree check calculus**, sound for the algebra of rational trees. Its refutations
are clashes; it uses no occurs check. -/
inductive Derives (problem : EquationStore (RTree σ)) (label : O → RTree σ) (world : Finset O) :
    Check (RTree σ) → Prop
  | equal {left right : RTree σ} : (rationalAction σ).Models (mgu problem) problem →
      RTree.subst (mgu problem) left = RTree.subst (mgu problem) right →
      Derives problem label world (.equal left right)
  | absent {pattern : RTree σ} : (rationalAction σ).Models (mgu problem) problem →
      (∀ o ∈ world, Refuted (problem ++ [(pattern, label o)])) →
      Derives problem label world (.absent pattern)
  | count {pattern : RTree σ} {number : Nat} : (rationalAction σ).Models (mgu problem) problem →
      (certain problem label world pattern).card = number →
      (∀ o ∈ world, RTree.subst (mgu problem) pattern = RTree.subst (mgu problem) (label o) ∨
        Refuted (problem ++ [(pattern, label o)])) →
      Derives problem label world (.count pattern number)

theorem refuted_iff_not_consistent (store : EquationStore (RTree σ)) :
    Refuted store ↔ ¬ (rationalAction σ).Consistent store := by
  rw [consistent_iff_not_refuted, not_not]

theorem consistent_append_iff (problem : EquationStore (RTree σ)) (s t : RTree σ) :
    (rationalAction σ).Consistent (problem ++ [(s, t)]) ↔
      ∃ θ, (rationalAction σ).Models θ problem ∧ (rationalAction σ).Solves θ (s, t) := by
  simp only [SubstitutionAction.Consistent, SubstitutionAction.models_append,
    SubstitutionAction.models_cons, SubstitutionAction.models_nil, and_true]

/-- An empty region of possible matches is a refutation of each occurrence. -/
theorem possible_empty_iff (problem : EquationStore (RTree σ)) (label : O → RTree σ)
    (world : Finset O) (pattern : RTree σ) :
    PrincipalCheckRegions.possibleRegion (rationalAction σ) problem label world pattern = ∅ ↔
      ∀ o ∈ world, Refuted (problem ++ [(pattern, label o)]) := by
  constructor
  · intro empty o present
    rw [refuted_iff_not_consistent]
    intro consistent
    have member : o ∈ PrincipalCheckRegions.possibleRegion (rationalAction σ) problem label world pattern := by
      obtain ⟨assignment, solved, same⟩ := (consistent_append_iff problem pattern (label o)).mp consistent
      exact (PrincipalCheckRegions.possible_member_iff _ problem label world pattern o).mpr
        ⟨present, assignment, solved, same⟩
    rw [empty] at member
    exact Finset.notMem_empty o member
  · intro refuted
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro o member
    obtain ⟨present, assignment, solved, same⟩ :=
      (PrincipalCheckRegions.possible_member_iff _ problem label world pattern o).mp member
    exact (refuted_iff_not_consistent _).mp (refuted o present)
      ((consistent_append_iff problem pattern (label o)).mpr ⟨assignment, solved, same⟩)

/-- The possible region is the certain one exactly when every other occurrence is refuted. -/
theorem possible_eq_certain_iff {problem : EquationStore (RTree σ)}
    (consistent : (rationalAction σ).Consistent problem) (label : O → RTree σ) (world : Finset O)
    (pattern : RTree σ) :
    PrincipalCheckRegions.possibleRegion (rationalAction σ) problem label world pattern =
        certain problem label world pattern ↔
      ∀ o ∈ world, RTree.subst (mgu problem) pattern = RTree.subst (mgu problem) (label o) ∨
        Refuted (problem ++ [(pattern, label o)]) := by
  have sound := (models_mgu_iff problem).mpr consistent
  have matchesIff : ∀ o, o ∈ certain problem label world pattern ↔
      o ∈ world ∧ RTree.subst (mgu problem) pattern = RTree.subst (mgu problem) (label o) := by
    intro o
    show o ∈ Check.matches (rationalAction σ) (mgu problem) label world pattern ↔ _
    classical
    simp only [Check.matches, Finset.mem_filter]
    exact Iff.rfl
  have possibleIff : ∀ o, o ∈ PrincipalCheckRegions.possibleRegion (rationalAction σ) problem label
      world pattern ↔ o ∈ world ∧ (rationalAction σ).Consistent (problem ++ [(pattern, label o)]) := by
    intro o
    exact (PrincipalCheckRegions.possible_member_iff _ problem label world pattern o).trans
      (and_congr Iff.rfl (consistent_append_iff problem pattern (label o)).symm)
  constructor
  · intro same o present
    by_cases possible : (rationalAction σ).Consistent (problem ++ [(pattern, label o)])
    · have member := (possibleIff o).mpr ⟨present, possible⟩
      rw [same] at member
      exact Or.inl ((matchesIff o).mp member).2
    · exact Or.inr ((refuted_iff_not_consistent _).mpr possible)
  · intro covered
    ext o
    rw [possibleIff, matchesIff]
    constructor
    · rintro ⟨present, possible⟩
      rcases covered o present with matched | refuted
      · exact ⟨present, matched⟩
      · exact absurd possible ((refuted_iff_not_consistent _).mp refuted)
    · rintro ⟨present, matched⟩
      refine ⟨present, mgu problem, ?_⟩
      exact ((rationalAction σ).models_append _ _ _).mpr ⟨sound, fun e member => by
        obtain rfl := List.mem_singleton.mp member
        exact matched⟩

/-- **Derivability is solvability and the ask**, over rational trees. -/
theorem derives_iff_entails (problem : EquationStore (RTree σ)) (label : O → RTree σ) (world : Finset O)
    (check : Check (RTree σ)) :
    Derives problem label world check ↔ (rationalAction σ).Consistent problem ∧
      (rationalAction σ).Entails problem fun θ => check.Holds (rationalAction σ) θ label world := by
  constructor
  · intro derivation
    cases derivation with
    | @equal left right solved same =>
        have consistent : (rationalAction σ).Consistent problem := ⟨_, solved⟩
        have principal := mgu_principal ((consistent_iff_not_refuted problem).mp consistent)
        exact ⟨consistent, (PrincipalCheckRegions.equal_iff_principal_answer (rationalAction σ)
          (SubstitutionAction.Principal.on _ principal [left, right]) left right (by simp) (by simp)).mpr same⟩
    | @absent pattern solved refuted =>
        exact ⟨⟨_, solved⟩, (PrincipalCheckRegions.absent_iff_possible_empty (rationalAction σ) problem
          label world pattern).mpr ((possible_empty_iff problem label world pattern).mpr refuted)⟩
    | @count pattern number solved card covered =>
        have consistent : (rationalAction σ).Consistent problem := ⟨_, solved⟩
        have principal := mgu_principal ((consistent_iff_not_refuted problem).mp consistent)
        refine ⟨consistent, (PrincipalCheckRegions.count_iff_regions (rationalAction σ)
          (SubstitutionAction.Principal.on _ principal (pattern :: world.toList.map label)) label world
          pattern number List.mem_cons_self (fun o present => List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr present, rfl⟩))).mpr ⟨card, ?_⟩⟩
        exact (possible_eq_certain_iff consistent label world pattern).mpr covered
  · rintro ⟨consistent, asked⟩
    have solved := (models_mgu_iff problem).mpr consistent
    have principal := mgu_principal ((consistent_iff_not_refuted problem).mp consistent)
    cases check with
    | equal left right =>
        exact .equal solved ((PrincipalCheckRegions.equal_iff_principal_answer (rationalAction σ)
          (SubstitutionAction.Principal.on _ principal [left, right]) left right (by simp) (by simp)).mp asked)
    | absent pattern =>
        exact .absent solved ((possible_empty_iff problem label world pattern).mp
          ((PrincipalCheckRegions.absent_iff_possible_empty (rationalAction σ) problem label world
            pattern).mp asked))
    | count pattern number =>
        obtain ⟨card, same⟩ := (PrincipalCheckRegions.count_iff_regions (rationalAction σ)
          (SubstitutionAction.Principal.on _ principal (pattern :: world.toList.map label)) label world
          pattern number List.mem_cons_self (fun o present => List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr present, rfl⟩))).mp asked
        exact .count solved card ((possible_eq_certain_iff consistent label world pattern).mp same)

/-- **Sound and complete for the rational tree algebra**: a check is derivable exactly when the store
has a point of the tree algebra and the check holds at every point satisfying the store. -/
theorem derives_iff_treeModel (problem : EquationStore (RTree σ)) (label : O → RTree σ)
    (world : Finset O) (check : Check (RTree σ)) :
    Derives problem label world check ↔
      (∃ ρ : RSubst σ, (treeModel σ).Models (a := PUnit.unit) ρ problem) ∧
      ∀ ρ : RSubst σ, (treeModel σ).Models (a := PUnit.unit) ρ problem →
        (treeModel σ).Satisfies (a := PUnit.unit) ρ (checkGuard label world check) := by
  rw [derives_iff_entails]
  exact and_congr Iff.rfl (forall_congr' fun ρ => imp_congr Iff.rfl
    (checkGuard_sat (rationalAction σ) ρ label world check).symm)

/-- **Consistency of the rational-tree check calculus**: for distinct constants, `c = d` is derivable
from no store. -/
theorem not_derives_clash {label : O → RTree σ} {c d : σ.constants} (distinct : c ≠ d)
    (problem : EquationStore (RTree σ)) (world : Finset O) :
    ¬ Derives problem label world (.equal (RTree.ofTerm (.const c)) (RTree.ofTerm (.const d))) := by
  intro derivation
  obtain ⟨⟨ρ, known⟩, valid⟩ := (derives_iff_treeModel problem label world _).mp derivation
  have holds : RTree.subst ρ (RTree.ofTerm (.const c)) = RTree.subst ρ (RTree.ofTerm (.const d)) :=
    valid ρ known
  have roots := congrFun (congrArg Subtype.val holds) []
  have constRoot : ∀ e : σ.constants, (RTree.subst ρ (RTree.ofTerm (.const e))).1 [] =
      some (.const e) := fun e =>
    Raw.subst_nil (θ := fun v => (ρ v).1) (t := Raw.ofTerm (.const e)) (fun v same => by cases same)
  rw [constRoot, constRoot] at roots
  exact distinct (Head.const.inj (Option.some.inj roots))

end RationalChecks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.treeModel
#print axioms Rational.treeModel_free
#print axioms Rational.entails_iff_treeModel
#print axioms Rational.models_mgu_iff
#print axioms Rational.RationalChecks.possible_empty_iff
#print axioms Rational.RationalChecks.possible_eq_certain_iff
#print axioms Rational.RationalChecks.derives_iff_entails
#print axioms Rational.RationalChecks.derives_iff_treeModel
#print axioms Rational.RationalChecks.not_derives_clash

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
