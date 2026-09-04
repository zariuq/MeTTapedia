import Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport
import Mettapedia.TypeTheory.SetFamilySemanticSpan

/-!
# Exact representation over the large set-family semantics

Exact code can be added pointwise to every dependent family in the large
set-family CwF.  Quotation and splicing commute with substitution and satisfy
beta and eta.  Independently, the small Tarski universe is fibrewise closed
under this representation operation: a code for a small type yields a code
whose decoding is equivalent to exact code over the original decoding.

This connects exact representation to the same semantic CwF already used for
simple HOL types, dependent products and sums, identity elimination, and
proof-relevant operational evidence.  It does not equip that CwF with a mode
theory, an operational communication rule, a locking discipline, or a cost
interpretation.  Those remain additional structures and laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SetFamilyExactCodeSemantics

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.BranchingEvidenceTarskiInterpretation
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
open Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation
open Mettapedia.TypeTheory.CwfTarskiUniverse.SetFamilies
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilyEquivalenceTransport
open Mettapedia.TypeTheory.ExactCodeFamilyRepresentation
open Mettapedia.TypeTheory.ExactCodeModalityModel
open Mettapedia.TypeTheory.SetFamilySemanticSpan

universe small v

/-! ## Exact code as a dependent-family operation -/

/-- Add exact representation layers fibrewise to a type of the large
set-family CwF. -/
def exactCodeType (depth : Nat) {context : Type (small + 1)}
    (family : semanticCwf.{small}.Ty context) :
    semanticCwf.{small}.Ty context :=
  ExactCodeFamilyRepresentation.codeFamily depth family

/-- Quote a section of a dependent family pointwise. -/
def quoteTerm (depth : Nat) {context : Type (small + 1)}
    {family : semanticCwf.{small}.Ty context}
    (term : semanticCwf.{small}.Tm context family) :
    semanticCwf.{small}.Tm context (exactCodeType depth family) :=
  quoteSection depth term

/-- Splice a pointwise exact-code section. -/
def spliceTerm (depth : Nat) {context : Type (small + 1)}
    {family : semanticCwf.{small}.Ty context}
    (term : semanticCwf.{small}.Tm context (exactCodeType depth family)) :
    semanticCwf.{small}.Tm context family :=
  spliceSection depth term

/-- Exact-code types commute definitionally with contextual substitution. -/
theorem exactCodeType_substitution (depth : Nat)
    {source target : Type (small + 1)}
    (family : semanticCwf.{small}.Ty target)
    (substitution : semanticCwf.{small}.Sub source target) :
    semanticCwf.{small}.tySub (exactCodeType depth family) substitution =
      exactCodeType depth
        (semanticCwf.{small}.tySub family substitution) :=
  rfl

/-- Quotation commutes definitionally with contextual substitution. -/
theorem quoteTerm_substitution (depth : Nat)
    {source target : Type (small + 1)}
    {family : semanticCwf.{small}.Ty target}
    (term : semanticCwf.{small}.Tm target family)
    (substitution : semanticCwf.{small}.Sub source target) :
    semanticCwf.{small}.tmSub (quoteTerm depth term) substitution =
      quoteTerm depth
        (semanticCwf.{small}.tmSub term substitution) :=
  rfl

/-- Splicing commutes definitionally with contextual substitution. -/
theorem spliceTerm_substitution (depth : Nat)
    {source target : Type (small + 1)}
    {family : semanticCwf.{small}.Ty target}
    (term : semanticCwf.{small}.Tm target (exactCodeType depth family))
    (substitution : semanticCwf.{small}.Sub source target) :
    semanticCwf.{small}.tmSub (spliceTerm depth term) substitution =
      spliceTerm depth
        (semanticCwf.{small}.tmSub term substitution) :=
  rfl

/-- Pointwise exact representation satisfies beta. -/
theorem splice_quote_term (depth : Nat)
    {context : Type (small + 1)}
    {family : semanticCwf.{small}.Ty context}
    (term : semanticCwf.{small}.Tm context family) :
    spliceTerm depth (quoteTerm depth term) = term :=
  splice_quote_section depth term

/-- Pointwise exact representation satisfies eta. -/
theorem quote_splice_term (depth : Nat)
    {context : Type (small + 1)}
    {family : semanticCwf.{small}.Ty context}
    (term : semanticCwf.{small}.Tm context (exactCodeType depth family)) :
    quoteTerm depth (spliceTerm depth term) = term :=
  quote_splice_section depth term

/-! ## Closure of the internal Tarski universe -/

/-- Lifting an iterated small code is equivalent to iterating exact code over
the lifted body. -/
def liftedIterEquiv (depth : Nat) (Body : Type small) :
    SmallLift.{small} (ExactCodeIter depth Body) ≃
      ExactCodeIter depth (SmallLift.{small} Body) :=
  (Equiv.ulift.trans (iterEquiv depth Body)).trans
    (Equiv.ulift.symm.trans
      (iterEquiv depth (SmallLift.{small} Body)).symm)

/-- Transform an internal code by adding exact representation layers to the
small type named by that code. -/
def exactCodeCode (depth : Nat) {context : Type (small + 1)}
    (code : semanticCwf.{small}.Tm context
      (smallTypes.{small}.univ context)) :
    semanticCwf.{small}.Tm context (smallTypes.{small}.univ context) :=
  fun point => ⟨ExactCodeIter depth (code point).down⟩

/-- Decoding the transformed internal code agrees fibrewise with exact code
over the original decoded family. -/
def decodedExactCodeEquiv (depth : Nat)
    {context : Type (small + 1)}
    (code : semanticCwf.{small}.Tm context
      (smallTypes.{small}.univ context))
    (point : context) :
    smallTypes.{small}.el (exactCodeCode depth code) point ≃
      exactCodeType depth (smallTypes.{small}.el code) point :=
  liftedIterEquiv depth (code point).down

/-- Internal exact-code construction commutes definitionally with
substitution of universe codes. -/
theorem exactCodeCode_substitution (depth : Nat)
    {source target : Type (small + 1)}
    (code : semanticCwf.{small}.Tm target
      (smallTypes.{small}.univ target))
    (substitution : semanticCwf.{small}.Sub source target) :
    semanticCwf.{small}.tmSub (exactCodeCode depth code) substitution =
      exactCodeCode depth
        (semanticCwf.{small}.tmSub code substitution) :=
  rfl

/-! ## The shared semantic span remains non-collapsed -/

/-- Every internally coded small family receives exact representation in the
same Tarski universe, while the operational evidence and simple/dependent
non-collapse theorems remain valid. -/
theorem exact_code_extends_shared_span_without_collapse
    {Base : Type} {Const : Ty Base → Type v}
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) :
    (∀ (depth : Nat) {context : Type 1}
        (code : semanticCwf.{0}.Tm context
          (smallTypes.{0}.univ context)) (point : context),
      Nonempty
        (smallTypes.{0}.el (exactCodeCode depth code) point ≃
          exactCodeType depth (smallTypes.{0}.el code) point)) ∧
      (¬ Nonempty
        (FamilyFactorization liftedCompletion
          (smallTypes.{0}.el branchEvidenceCode))) ∧
      (∀ A : Ty Base,
        ¬ (∀ point : BoolContext.{0},
          Nonempty
            (smallTypes.{0}.el varyingCode point ≃
              AdmissibleValue
                (liftedStandardModel SmallCarrier constantDenotation) A))) :=
  by
    refine ⟨?_,
      (semanticSpan SmallCarrier constantDenotation).branchEvidenceNotCompletion,
      (semanticSpan SmallCarrier constantDenotation).varyingUniverseNotSimple⟩
    intro depth context code point
    exact ⟨decodedExactCodeEquiv depth code point⟩

/-! ## Positive and negative controls -/

/-- Positive: the internal Boolean code has a one-layer exact-code decoding
in the large semantic universe. -/
theorem bool_code_has_internal_exact_representation :
    Nonempty
      (smallTypes.{0}.el
          (exactCodeCode 1 boolTypeCode)
          (⟨PUnit.unit⟩ : UnitContext) ≃
        ExactCodeIter 1
          (smallTypes.{0}.el boolTypeCode
            (⟨PUnit.unit⟩ : UnitContext))) :=
  ⟨decodedExactCodeEquiv 1 boolTypeCode
    (⟨PUnit.unit⟩ : UnitContext)⟩

/-- The exact-code transform of the internal operational-evidence code
decodes to exact code over the original proof-relevant evidence fibre. -/
def exactBranchEvidenceEquiv (depth : Nat) (state : SourceTerm) :
    smallTypes.{0}.el
        (exactCodeCode depth branchEvidenceCode)
        (ULift.up state) ≃
      ExactCodeIter depth (exactFamily.Exact state) :=
  (decodedExactCodeEquiv depth branchEvidenceCode (ULift.up state)).trans
    (iterCongrEquiv depth (branchEvidenceEquiv state))

/-- Exact representation retains, rather than hides, the obstruction to
descending proof-relevant branch evidence through completion. -/
theorem exact_branch_evidence_does_not_factor_through_completion
    (depth : Nat) :
    ¬ Nonempty
      (FamilyFactorization liftedCompletion
        (exactCodeType depth
          (smallTypes.{0}.el branchEvidenceCode))) := by
  simpa [exactCodeType] using
    (codeFamily_nonfactorization_iff depth liftedCompletion
      (smallTypes.{0}.el branchEvidenceCode)).2
        decodedEvidence_does_not_factor_through_completion

/-- Negative: internal exact-code closure does not repair the deliberately
coarse completion observer for operational evidence. -/
theorem internal_exact_code_does_not_make_completion_evidence_complete :
    ¬ Nonempty
      (FamilyFactorization liftedCompletion
        (smallTypes.{0}.el branchEvidenceCode)) :=
  decodedEvidence_does_not_factor_through_completion

#print axioms exactCodeType_substitution
#print axioms quoteTerm_substitution
#print axioms spliceTerm_substitution
#print axioms splice_quote_term
#print axioms quote_splice_term
#print axioms liftedIterEquiv
#print axioms decodedExactCodeEquiv
#print axioms exactCodeCode_substitution
#print axioms exact_code_extends_shared_span_without_collapse
#print axioms bool_code_has_internal_exact_representation
#print axioms exactBranchEvidenceEquiv
#print axioms exact_branch_evidence_does_not_factor_through_completion
#print axioms internal_exact_code_does_not_make_completion_evidence_complete

end Mettapedia.TypeTheory.SetFamilyExactCodeSemantics
