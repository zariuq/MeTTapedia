import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalModels

/-!
# Admission over rational trees as derivation

This mirrors the admission part of `ModelDerivation` for the rational-tree fibre.

* **Derivable admission** (`RationalChecks.AdmitsDerivably`): a firing's shapes and enabling, the
  solved form solving its information, and a derivation in the rational-tree check calculus of each
  of its checks from its information.
* **A query-free firing is admitted over rational trees exactly when its admission is derivable**
  (`admitsDerivably_iff`).
* **Consistency for firings** (`not_admitsDerivably_clash`): for distinct constants, the admission
  of the firing that tells `c = d` is not derivable at any configuration. The rational-tree step
  admits `X = f(X)` (`RationalStep`), but never `c = d`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP
open Interface (Frames)
open AnnotatedRuns (Firing firstOrder firstOrder_admits_iff)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

variable {σ : LPSignature} {O : Type} [DecidableEq O]

/-- The firing that tells `c = d` over rational trees, and does nothing else. -/
def tellClash (c d : σ.constants) : Firing (RTree σ) (RSubst σ) O :=
  ⟨⟨[], [], [(RTree.ofTerm (.const c), RTree.ofTerm (.const d))], [], []⟩, [], ⟨[], [], []⟩⟩

/-- Substitution keeps a constant. -/
theorem subst_const_root (ρ : RSubst σ) (c : σ.constants) :
    (RTree.subst ρ (RTree.ofTerm (.const c))).1 [] = some (.const c) :=
  Raw.subst_nil (θ := fun v => (ρ v).1) (t := Raw.ofTerm (.const c)) (fun v same => by cases same)

/-- **Distinct constants are never identified by a rational substitution.** -/
theorem subst_const_ne (ρ : RSubst σ) {c d : σ.constants} (distinct : c ≠ d) :
    RTree.subst ρ (RTree.ofTerm (.const c)) ≠ RTree.subst ρ (RTree.ofTerm (.const d)) := by
  intro same
  have roots := congrFun (congrArg Subtype.val same) []
  rw [subst_const_root, subst_const_root] at roots
  exact distinct (Head.const.inj (Option.some.inj roots))

namespace RationalChecks

variable (label : O → RTree σ)

/-- **Derivable admission over rational trees.** -/
def AdmitsDerivably (C : Configuration (RTree σ) O) (f : Firing (RTree σ) (RSubst σ) O) : Prop :=
  (firstOrder (rationalAction σ) label).Shapes (s := C) f ∧
    Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
    (rationalAction σ).Models (mgu (f.selection.problem label f.rule C)) (f.selection.problem label f.rule C) ∧
    ∀ check ∈ f.rule.checks, Derives (f.selection.problem label f.rule C) label C.present check

/-- **A query-free firing is admitted over rational trees exactly when its admission is
derivable.** -/
theorem admitsDerivably_iff {C : Configuration (RTree σ) O} {f : Firing (RTree σ) (RSubst σ) O}
    (noQueries : f.queries = []) :
    AdmitsDerivably label C f ↔ f.Valid (rationalAction σ) label C := by
  rw [firstOrder_admits_iff, Frames.ofSubstitution_solvable_iff]
  unfold AdmitsDerivably
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [models_mgu_iff]
  constructor
  · rintro ⟨solvable, derived⟩
    refine ⟨solvable, fun b θ solved => ⟨fun check member =>
      ((derives_iff_entails _ label C.present check).mp (derived check member)).2 θ solved, ?_⟩⟩
    intro query member
    rw [noQueries] at member
    cases member
  · rintro ⟨solvable, asked⟩
    exact ⟨solvable, fun check member => (derives_iff_entails _ label C.present check).mpr
      ⟨solvable, fun θ solved => (asked PUnit.unit θ solved).1 check member⟩⟩

variable {label}

/-- **The admission of the firing that tells `c = d` is not derivable**, at any configuration. -/
theorem not_admitsDerivably_clash {c d : σ.constants} (distinct : c ≠ d)
    (C : Configuration (RTree σ) O) : ¬ AdmitsDerivably label C (tellClash (O := O) c d) := by
  rintro ⟨_, _, solved, _⟩
  have told := solved (RTree.ofTerm (.const c), RTree.ofTerm (.const d))
    (by simp [Selection.problem, tellClash])
  exact subst_const_ne _ distinct told

/-- **Consistency of the rational-tree calculus**, for checks and for firings. -/
theorem rationalChecks_consistent {c d : σ.constants} (distinct : c ≠ d) :
    (∀ (problem : EquationStore (RTree σ)) (world : Finset O),
      ¬ Derives problem label world (.equal (RTree.ofTerm (.const c)) (RTree.ofTerm (.const d)))) ∧
      ∀ C : Configuration (RTree σ) O, ¬ AdmitsDerivably label C (tellClash (O := O) c d) :=
  ⟨fun problem world => not_derives_clash distinct problem world,
    fun C => not_admitsDerivably_clash distinct C⟩

end RationalChecks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.subst_const_ne
#print axioms Rational.RationalChecks.admitsDerivably_iff
#print axioms Rational.RationalChecks.not_admitsDerivably_clash
#print axioms Rational.RationalChecks.rationalChecks_consistent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
