import Mettapedia.Computability.DependentEvidenceComparison
import Mettapedia.Computability.OpenComputationalTrinity
import Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport

/-!
# Exact representation of dependent-evidence comparisons

Pointwise exact code changes the representation of dependent evidence without
changing its state index.  It therefore induces mutually inverse development
maps between the coded and uncoded computational-trinity comparisons.
Program-information loss, direct-observation faithfulness, and failure of an
authentic cost to descend through a coarse observer are all invariant under
this change of representation.

This is a representation theorem.  It does not add a modal discipline,
operational communication, effects, scheduling, or a cost interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ExactCodeDependentEvidenceComparison

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.DependentEvidenceComparison
open Mettapedia.Computability.OpenComputationalTrinity
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport
open Mettapedia.TypeTheory.ExactCodeFamilyRepresentation

universe u

variable {State View : Type u}

/-- The total coded-evidence carrier is equivalent to the original total
evidence carrier, with the state index retained definitionally. -/
def codeTotalEquiv (depth : Nat) (evidence : State → Type u) :
    TotalEvidence (codeFamily depth evidence) ≃ TotalEvidence evidence :=
  totalEvidenceEquiv (codeFamilyEquiv depth evidence)

@[simp] theorem codeTotalEquiv_fst (depth : Nat)
    (evidence : State → Type u)
    (total : TotalEvidence (codeFamily depth evidence)) :
    (codeTotalEquiv depth evidence total).1 = total.1 :=
  rfl

/-- Exact representation gives a natural isomorphism of the program faces. -/
def codeProgramIso (depth : Nat) (evidence : State → Type u) :
    evidenceFace (codeFamily depth evidence) ≅ evidenceFace evidence :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).mapIso
    (codeTotalEquiv depth evidence).toIso

/-- Splicing exact evidence is a commuting development from the coded
comparison to the original comparison. -/
def spliceComparisonMap (depth : Nat) (evidence : State → Type u)
    (observe : State → View) :
    ComparisonMap (comparison (codeFamily depth evidence) observe)
      (comparison evidence observe) where
  program := (codeProgramIso depth evidence).hom
  logic := 𝟙 (stateFace (State := State))
  space := 𝟙 (viewFace (View := View))
  programLogic := by
    ext context total
    rfl
  logicSpace := by simp [comparison]

/-- Quotation gives the inverse commuting development. -/
def quoteComparisonMap (depth : Nat) (evidence : State → Type u)
    (observe : State → View) :
    ComparisonMap (comparison evidence observe)
      (comparison (codeFamily depth evidence) observe) where
  program := (codeProgramIso depth evidence).inv
  logic := 𝟙 (stateFace (State := State))
  space := 𝟙 (viewFace (View := View))
  programLogic := by
    ext context total
    rfl
  logicSpace := by simp [comparison]

/-- Splice followed by quote is the identity on the coded program face. -/
theorem splice_quote_program_map (depth : Nat)
    (evidence : State → Type u) (observe : State → View) :
    (spliceComparisonMap depth evidence observe).program ≫
        (quoteComparisonMap depth evidence observe).program =
      𝟙 (evidenceFace (codeFamily depth evidence)) :=
  (codeProgramIso depth evidence).hom_inv_id

/-- Quote followed by splice is the identity on the original program face. -/
theorem quote_splice_program_map (depth : Nat)
    (evidence : State → Type u) (observe : State → View) :
    (quoteComparisonMap depth evidence observe).program ≫
        (spliceComparisonMap depth evidence observe).program =
      𝟙 (evidenceFace evidence) :=
  (codeProgramIso depth evidence).inv_hom_id

/-- Exact representation preserves and reflects loss of program information
through the selected state observer. -/
theorem exactCode_comparison_loses_iff (depth : Nat)
    (evidence : State → Type u) (observe : State → View) :
    (comparison (codeFamily depth evidence) observe).LosesProgramInformation ↔
      (comparison evidence observe).LosesProgramInformation :=
  comparison_loses_congr_fibreEquiv observe
    (codeFamilyEquiv depth evidence)

/-- Direct observational faithfulness is likewise invariant under exact
representation. -/
theorem exactCode_direct_injective_iff (depth : Nat)
    (evidence : State → Type u) (observe : State → View) :
    Function.Injective
        (fun total : TotalEvidence (codeFamily depth evidence) =>
          observe total.1) ↔
      Function.Injective
        (fun total : TotalEvidence evidence => observe total.1) := by
  let equivalence := codeTotalEquiv depth evidence
  constructor
  · intro codedInjective left right sameView
    have codedEqual : equivalence.symm left = equivalence.symm right :=
      codedInjective sameView
    calc
      left = equivalence (equivalence.symm left) :=
        (equivalence.apply_symm_apply left).symm
      _ = equivalence (equivalence.symm right) :=
        congrArg equivalence codedEqual
      _ = right := equivalence.apply_symm_apply right
  · intro rawInjective left right sameView
    apply equivalence.injective
    exact rawInjective sameView

/-! ## Branching and cost canary -/

namespace Canary

open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization

/-- Exact representation does not repair the branch-evidence distinction
lost by the completion observer. -/
theorem exact_code_branching_still_loses (depth : Nat) :
    (comparison (codeFamily depth exactFamily.Exact)
      sourceCompletion.observe).LosesProgramInformation :=
  (exactCode_comparison_loses_iff depth exactFamily.Exact
    sourceCompletion.observe).2
      Mettapedia.Computability.DependentEvidenceComparison.Canary.branching_comparison_loses_program_information

/-- Authentic operational work/span transported to coded total evidence. -/
def codedWorkSpan (depth : Nat) :
    TotalEvidence (codeFamily depth exactFamily.Exact) →
      Mettapedia.Algebra.WorkSpan :=
  Mettapedia.Computability.DependentEvidenceComparison.Canary.totalEvidenceWorkSpan ∘
    codeTotalEquiv depth exactFamily.Exact

/-- Exact representation preserves the cost obstruction: completion still
cannot reconstruct authentic work/span. -/
theorem exact_code_workSpan_does_not_factor (depth : Nat) :
    ¬ Factors
      (fun total : TotalEvidence (codeFamily depth exactFamily.Exact) =>
        sourceCompletion.observe total.1)
      (codedWorkSpan depth) := by
  let equivalence := codeTotalEquiv depth exactFamily.Exact
  have transported :=
    (not_factors_precomp_equiv_iff equivalence
      (fun total : TotalEvidence exactFamily.Exact =>
        sourceCompletion.observe total.1)
      Mettapedia.Computability.DependentEvidenceComparison.Canary.totalEvidenceWorkSpan).2
        Mettapedia.Computability.DependentEvidenceComparison.Canary.workSpan_does_not_factor_through_completion
  simpa [codedWorkSpan, Function.comp_def, equivalence] using transported

/-- Paired canary: exact code preserves both observational loss and the
independent cost obstruction. -/
theorem exact_code_preserves_operational_boundary (depth : Nat) :
    (comparison (codeFamily depth exactFamily.Exact)
        sourceCompletion.observe).LosesProgramInformation ∧
      ¬ Factors
        (fun total : TotalEvidence (codeFamily depth exactFamily.Exact) =>
          sourceCompletion.observe total.1)
        (codedWorkSpan depth) :=
  ⟨exact_code_branching_still_loses depth,
    exact_code_workSpan_does_not_factor depth⟩

end Canary

#print axioms codeTotalEquiv
#print axioms codeProgramIso
#print axioms spliceComparisonMap
#print axioms quoteComparisonMap
#print axioms splice_quote_program_map
#print axioms quote_splice_program_map
#print axioms exactCode_comparison_loses_iff
#print axioms exactCode_direct_injective_iff
#print axioms Canary.exact_code_branching_still_loses
#print axioms Canary.exact_code_workSpan_does_not_factor
#print axioms Canary.exact_code_preserves_operational_boundary

end Mettapedia.Computability.ExactCodeDependentEvidenceComparison
