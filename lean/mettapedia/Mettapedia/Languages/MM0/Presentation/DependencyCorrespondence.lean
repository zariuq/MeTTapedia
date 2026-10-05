import Mettapedia.Languages.MM0.Presentation.DependencyProgram

/-!
# Computational correspondence for MM0 dependency pairs

The equation program agrees with the independent check on every context,
binder and expression. With a supported target expression, its Boolean answer
is exactly the declarative independence condition. That support premise is
supplied by argument typing in the complete admissible-substitution check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDependency

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => dependencyProgram
local notation "H" => computationalHost

private theorem support_disjoint :
    ∀ equation ∈ naturalMembershipProgram ++ dependencyEquations,
      equation.head ∉ ComputationalSupport.supportProgram.calledHeads := by decide

private theorem membership_before_disjoint :
    ∀ equation ∈ ComputationalSupport.supportProgram,
      equation.head ∉ naturalMembershipProgram.calledHeads := by decide

private theorem membership_after_disjoint :
    ∀ equation ∈ dependencyEquations,
      equation.head ∉ naturalMembershipProgram.calledHeads := by decide

theorem support_reused (context : Context) (expression : Preterm) :
    Applies P H "mm0:support" [encodeContext context, encode expression]
      (ComputationalSupport.encodeResult (ComputationalSupport.indices? context expression)) := by
  exact (Applies.append_iff ComputationalSupport.supportProgram
    (naturalMembershipProgram ++ dependencyEquations) H support_disjoint "mm0:support"
    (by decide) _ _).mpr (ComputationalSupport.support_computes context expression)

theorem membership_reused (index : Nat) (values : List Nat) :
    Applies P H "nik:nat-member" [natural index, encodeNaturals values]
      (boolean (decide (index ∈ values))) := by
  exact (Applies.frame_iff naturalMembershipProgram ComputationalSupport.supportProgram
    dependencyEquations H membership_before_disjoint membership_after_disjoint "nik:nat-member"
    (by decide) _ _).mpr (natural_membership_computes index values)

theorem depends_computes (binder : Kernel.Binder) (position index : Nat) :
    Applies P H "mm0:depends" [encodeBinder binder, natural position, natural index]
      (boolean (decide (binder.DependsOn position index))) := by
  cases binder with
  | bound sort =>
    refine Applies.equation (equation := P[55])
      (environment := [("sort", natural sort), ("position", natural position), ("index", natural index)])
      (by rfl) (by rfl) ?_
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
      (.primitive (by rfl) (computationalHost_binary (operation := .equal) rfl _ _ (by decide) (by decide)))
  | regular sort dependencies =>
    refine Applies.equation (equation := P[56])
      (environment := [("sort", natural sort), ("dependencies", encodeDependencies dependencies),
        ("position", natural position), ("index", natural index)]) (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ?_
    simpa only [encodeDependencies, Kernel.Binder.DependsOn, Finset.mem_sort] using
      membership_reused index (dependencies.sort (· ≤ ·))

private theorem negate_computes (value : Bool) :
    Applies P H "mm0:dependency-not" [boolean value] (boolean (!value)) := by
  cases value <;> exact ⟨1, rfl⟩

private def avoids (indices : Option (List Nat)) (index : Nat) : Bool :=
  match indices with
  | none => false
  | some values => !(decide (index ∈ values))

private theorem support_disjoint_computes (indices : Option (List Nat)) (index : Nat) :
    Applies P H "mm0:support-disjoint" [ComputationalSupport.encodeResult indices, natural index]
      (boolean (avoids indices index)) := by
  cases indices with
  | none => exact ⟨1, rfl⟩
  | some values =>
    refine Applies.equation (equation := P[61])
      (environment := [("indices", encodeNaturals values), ("target-bound", natural index)])
      (by rfl) (by rfl) ?_
    refine Evaluates.call (by simp [Special]) (.cons ?_ .nil) (negate_computes _)
    exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (membership_reused index values)

private theorem independent_computes (target : Context) (index : Nat) (expression : Preterm) :
    Applies P H "mm0:pair-depends" [.sym "False", encodeContext target, natural index, encode expression]
      (boolean (avoids (ComputationalSupport.indices? target expression) index)) := by
  refine Applies.equation (equation := P[59])
    (environment := [("target", encodeContext target), ("target-bound", natural index),
      ("expression", encode expression)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
    (support_disjoint_computes _ index)
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (support_reused target expression)

private theorem avoids_meaning (target : Context) (expression : Preterm) (index : Nat) :
    avoids (ComputationalSupport.indices? target expression) index =
      (match Preterm.support? target expression with
       | none => false
       | some support => decide (index ∉ support)) := by
  rw [← ComputationalSupport.indices_meaning]
  cases ComputationalSupport.indices? target expression <;> simp [avoids]

theorem pair_computes (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) :
    Applies P H "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression]
      (boolean (Substitution.checkPair target formalBound targetBound ((binder, expression), position))) := by
  refine Applies.equation (equation := P[57])
    (environment := [("target", encodeContext target), ("formal-bound", natural formalBound),
      ("target-bound", natural targetBound), ("binder", encodeBinder binder),
      ("position", natural position), ("expression", encode expression)]) (by rfl) (by rfl) ?_
  refine Evaluates.call
    (values := [boolean (decide (binder.DependsOn position formalBound)), encodeContext target,
      natural targetBound, encode expression]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) .nil)))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
      (depends_computes binder position formalBound)
  · by_cases dependent : binder.DependsOn position formalBound
    · simp only [Substitution.checkPair, dependent, ↓reduceIte, decide_true, boolean]
      exact ⟨1, rfl⟩
    · have step := independent_computes target targetBound expression
      rw [avoids_meaning] at step
      cases supported : Preterm.support? target expression <;>
        simpa [Substitution.checkPair, dependent, supported, boolean] using step

theorem pair_result_exact (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) (result : Term) :
    Applies P H "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression] result ↔
      result = boolean (Substitution.checkPair target formalBound targetBound ((binder, expression), position)) := by
  constructor
  · exact fun run => run.deterministic (pair_computes target formalBound targetBound binder position expression)
  · rintro rfl
    exact pair_computes target formalBound targetBound binder position expression

theorem pair_accepts_iff (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) {support : Finset Nat}
    (supported : Preterm.Supports target expression support) :
    Applies P H "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression] (.sym "True") ↔
      Substitution.PairIndependent target formalBound targetBound ((binder, expression), position) := by
  rw [pair_result_exact, ← Substitution.checkPair_iff supported]
  cases Substitution.checkPair target formalBound targetBound ((binder, expression), position) <;>
    simp [boolean]

theorem pair_completed_result (target : Context) (formalBound targetBound : Nat)
    (binder : Kernel.Binder) (position : Nat) (expression : Preterm) (fuel : Nat)
    (finished : apply P H fuel "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression] ≠ .exhausted) :
    apply P H fuel "mm0:check-pair"
      [encodeContext target, natural formalBound, natural targetBound,
        encodeBinder binder, natural position, encode expression] =
      .value (boolean (Substitution.checkPair target formalBound targetBound ((binder, expression), position))) :=
  (pair_computes target formalBound targetBound binder position expression).completed fuel finished

end Mettapedia.Languages.MM0.Presentation.ComputationalDependency
