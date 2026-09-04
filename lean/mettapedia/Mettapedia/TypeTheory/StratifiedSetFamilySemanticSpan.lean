import Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
import Mettapedia.TypeTheory.ExactCodeModalityModel
import Mettapedia.TypeTheory.SetFamilySemanticSpan

/-!
# A stratified set-family span for simple, dependent, operational, and code semantics

The two-level set-family hierarchy can carry four independently specified
faces at once:

* a property-explicit standard interpretation of simple HOL types and terms;
* dependent products, sums, identity elimination, and a cumulative Tarski
  hierarchy;
* proof-relevant operational evidence which does not descend through a coarse
  completion observer; and
* exact representation layers together with authentic event-cost valuations.

The construction is a compatibility theorem.  It does not identify simple
and dependent typing, operational evidence and visible answers, code and
execution, or cost and denotation.  It also does not select a proof calculus,
identity policy, conversion algorithm, or product language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.StratifiedSetFamilySemanticSpan

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualEffectValuation
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
open Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy
open Mettapedia.TypeTheory.CwfTarskiUniverseHierarchy.TwoLevelSetFamilies
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.ExactCodeModalityModel

universe v

variable {Base : Type} {Const : Ty Base → Type v}

/-- The shared semantic CwF lives two universes above the small carriers. -/
abbrev sharedCwf := TwoLevelSetFamilies.semanticCwf.{0}

/-- Standard-model contexts lifted into the context universe of `sharedCwf`. -/
abbrev HolContext
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    (context : Ctx Base) : Type 2 :=
  ULift.{2, 1}
    (AdmissibleContext
      (liftedStandardModel SmallCarrier constantDenotation) context)

/-- Simultaneous HOL substitution interpreted in the lifted semantic
contexts. -/
def interpretHolSubstitution
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    {source target : Ctx Base}
    (substitution :
      (ContextualStructure.holScwf Base Const).Sub source target) :
    HolContext SmallCarrier constantDenotation source →
      HolContext SmallCarrier constantDenotation target :=
  fun valuation =>
    ⟨interpretSubstitution
      (liftedStandardModel SmallCarrier constantDenotation)
      substitution valuation.down⟩

/-- A simple HOL type represented at the lower Tarski level.  The actual
constant interpretation remains an explicit parameter. -/
def interpretedHolTypeCode
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    {context : Ctx Base} (A : Ty Base) :
    sharedCwf.Tm
      (HolContext SmallCarrier constantDenotation context)
      (hierarchy.{0}.univ
        (HolContext SmallCarrier constantDenotation context) false) :=
  fun _ => ⟨SmallDenote SmallCarrier A⟩

/-- Decoding a lower-level HOL code recovers its admissible-value semantics. -/
def decodedHolTypeEquiv
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    {context : Ctx Base} (A : Ty Base)
    (valuation : HolContext SmallCarrier constantDenotation context) :
    hierarchy.{0}.el
        (interpretedHolTypeCode SmallCarrier constantDenotation A)
        valuation ≃
      AdmissibleValue
        (liftedStandardModel SmallCarrier constantDenotation) A :=
  Equiv.ulift.trans
    (decodedAdmissibleTypeEquiv
      SmallCarrier constantDenotation A valuation.down)

/-- A HOL term interpreted as a section of its lower-level decoding. -/
def codedHolTerm
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    {context : Ctx Base} {A : Ty Base}
    (term : Term Const context A) :
    sharedCwf.Tm
      (HolContext SmallCarrier constantDenotation context)
      (hierarchy.{0}.el
        (interpretedHolTypeCode SmallCarrier constantDenotation A)) :=
  fun valuation =>
    (decodedHolTypeEquiv
      SmallCarrier constantDenotation A valuation).symm
        (interpretTerm
          (liftedStandardModel SmallCarrier constantDenotation)
          term valuation.down)

/-- The lower-level HOL term interpretation commutes with simultaneous
substitution. -/
theorem codedHolTerm_substitution
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    {source target : Ctx Base} {A : Ty Base}
    (term : Term Const target A)
    (substitution :
      (ContextualStructure.holScwf Base Const).Sub source target) :
    sharedCwf.tmSub
        (codedHolTerm SmallCarrier constantDenotation term)
        (interpretHolSubstitution
          SmallCarrier constantDenotation substitution) =
      codedHolTerm SmallCarrier constantDenotation
        ((ContextualStructure.holScwf Base Const).tmSub term substitution) := by
  funext valuation
  exact congrArg
    (decodedHolTypeEquiv
      SmallCarrier constantDenotation A valuation).symm
    (interpretTerm_substitution
      (liftedStandardModel SmallCarrier constantDenotation)
      term substitution valuation.down).symm

/-! ## Operational evidence at the lower universe level -/

abbrev OperationalContext : Type 2 := ULift.{2, 0} SourceTerm

def completion : OperationalContext → Bool :=
  fun state => sourceCompletion.observe state.down

/-- Exact branch evidence represented at the lower universe level. -/
def branchEvidenceCode :
    sharedCwf.Tm OperationalContext
      (hierarchy.{0}.univ OperationalContext false) :=
  fun state => ⟨exactFamily.Exact state.down⟩

def branchEvidenceEquiv (state : SourceTerm) :
    hierarchy.{0}.el branchEvidenceCode (ULift.up state) ≃
      exactFamily.Exact state :=
  lowerDecodeEquiv.{0} (branchEvidenceCode (ULift.up state))

theorem branch_evidence_does_not_factor_through_completion :
    ¬ Nonempty
      (FamilyFactorization completion
        (hierarchy.{0}.el branchEvidenceCode)) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := ULift.up SourceTerm.leftDone)
    (right := ULift.up SourceTerm.rightDone)
    (by rfl)
  rintro ⟨equivalence⟩
  have unitBool : PUnit ≃ Bool :=
    (branchEvidenceEquiv SourceTerm.leftDone).symm.trans
      (equivalence.trans (branchEvidenceEquiv SourceTerm.rightDone))
  exact
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool
      ⟨unitBool⟩

/-- Exact representation remains a lower-level code because it preserves the
small evidence universe. -/
def exactBranchEvidenceCode (depth : Nat) :
    sharedCwf.Tm OperationalContext
      (hierarchy.{0}.univ OperationalContext false) :=
  fun state => ⟨ExactCodeIter depth (exactFamily.Exact state.down)⟩

def exactBranchEvidenceEquiv (depth : Nat) (state : SourceTerm) :
    hierarchy.{0}.el (exactBranchEvidenceCode depth) (ULift.up state) ≃
      ExactCodeIter depth (exactFamily.Exact state) :=
  lowerDecodeEquiv.{0}
    (exactBranchEvidenceCode depth (ULift.up state))

theorem exact_branch_evidence_does_not_factor_through_completion
    (depth : Nat) :
    ¬ Nonempty
      (FamilyFactorization completion
        (hierarchy.{0}.el (exactBranchEvidenceCode depth))) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := ULift.up SourceTerm.leftDone)
    (right := ULift.up SourceTerm.rightDone)
    (by rfl)
  rintro ⟨equivalence⟩
  have codedUnitBool : ExactCodeIter depth PUnit ≃
      ExactCodeIter depth Bool :=
    (exactBranchEvidenceEquiv depth SourceTerm.leftDone).symm.trans
      (equivalence.trans
        (exactBranchEvidenceEquiv depth SourceTerm.rightDone))
  have unitBool : PUnit ≃ Bool :=
    (iterEquiv depth PUnit).symm.trans
      (codedUnitBool.trans (iterEquiv depth Bool))
  exact
    Mettapedia.TypeTheory.DependentFamilyObserverFactorization.Canary.unit_not_equiv_bool
      ⟨unitBool⟩

/-! ## The simple image remains proper -/

abbrev BoolContext : Type 2 := ULift.{2, 0} Bool

def varyingCode :
    sharedCwf.Tm BoolContext (hierarchy.{0}.univ BoolContext false) :=
  fun point => ⟨if point.down then Bool else PUnit⟩

def varyingFalseEquiv :
    hierarchy.{0}.el varyingCode (ULift.up false) ≃ PUnit :=
  lowerDecodeEquiv.{0} (varyingCode (ULift.up false))

def varyingTrueEquiv :
    hierarchy.{0}.el varyingCode (ULift.up true) ≃ Bool :=
  lowerDecodeEquiv.{0} (varyingCode (ULift.up true))

theorem varying_code_not_a_simple_hol_type
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A)
    (A : Ty Base) :
    ¬ (∀ point : BoolContext,
      Nonempty
        (hierarchy.{0}.el varyingCode point ≃
          AdmissibleValue
            (liftedStandardModel SmallCarrier constantDenotation) A)) := by
  intro equivalent
  rcases equivalent (ULift.up false) with ⟨atFalse⟩
  rcases equivalent (ULift.up true) with ⟨atTrue⟩
  have unitBool : PUnit ≃ Bool :=
    varyingFalseEquiv.symm.trans
      ((atFalse.trans atTrue.symm).trans varyingTrueEquiv)
  have sameCardinality := Fintype.card_congr unitBool
  norm_num at sameCardinality

/-! ## Joint capability span -/

/-- Evidence that the extensional, dependent, operational, reflective, and
cost faces coexist in one stratified semantic model without collapsing their
distinctions. -/
structure SemanticSpan
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) where
  holTypeCodes : ∀ (context : Ctx Base) (A : Ty Base)
    (valuation : HolContext SmallCarrier constantDenotation context),
    Nonempty
      (hierarchy.{0}.el
          (interpretedHolTypeCode SmallCarrier constantDenotation A)
          valuation ≃
        AdmissibleValue
          (liftedStandardModel SmallCarrier constantDenotation) A)
  holTermSubstitution : ∀ {source target : Ctx Base} {A : Ty Base}
    (term : Term Const target A)
    (substitution :
      (ContextualStructure.holScwf Base Const).Sub source target),
    sharedCwf.tmSub
        (codedHolTerm SmallCarrier constantDenotation term)
        (interpretHolSubstitution
          SmallCarrier constantDenotation substitution) =
      codedHolTerm SmallCarrier constantDenotation
        ((ContextualStructure.holScwf Base Const).tmSub term substitution)
  products : Nonempty (DependentProductBeta sharedCwf)
  sums : Nonempty (DependentSumBeta sharedCwf)
  identity : Nonempty
    (IdentityEliminationBeta sharedCwf
      Families.identityFormation Families.identityReflexivity)
  hierarchySubstitution : Nonempty hierarchy.{0}.SubstitutionStable
  hierarchyCumulative : Nonempty
    (hierarchy.{0}.StrictlyCumulative Below)
  hierarchyProducts : Nonempty FibrewisePiClosed.{0}
  hierarchySums : Nonempty FibrewiseSigmaClosed.{0}
  hierarchyPredicative : externalFamily.{0}.PredicativeRanks
  hierarchyNotReversible :
    ¬ Nonempty (externalFamily.{0}.Cumulative ReverseBelow)
  operationalEvidenceCodes : ∀ state, Nonempty
    (hierarchy.{0}.el branchEvidenceCode (ULift.up state) ≃
      exactFamily.Exact state)
  operationalEvidenceNotCompletion :
    ¬ Nonempty
      (FamilyFactorization completion
        (hierarchy.{0}.el branchEvidenceCode))
  exactEvidenceCodes : ∀ depth state, Nonempty
    (hierarchy.{0}.el (exactBranchEvidenceCode depth) (ULift.up state) ≃
      ExactCodeIter depth (exactFamily.Exact state))
  exactEvidenceNotCompletion : ∀ depth,
    ¬ Nonempty
      (FamilyFactorization completion
        (hierarchy.{0}.el (exactBranchEvidenceCode depth)))
  varyingUniverseNotSimple : ∀ A : Ty Base,
    ¬ (∀ point : BoolContext,
      Nonempty
        (hierarchy.{0}.el varyingCode point ≃
          AdmissibleValue
            (liftedStandardModel SmallCarrier constantDenotation) A))
  sequentialWorkSpan :
    sharedGrade sequentialWorkSpanValuation evidenceProgram () = some ⟨3, 3⟩
  parallelWorkSpan :
    sharedGrade parallelWorkSpanValuation evidenceProgram () = some ⟨3, 2⟩
  visibleAnswerDoesNotDetermineCost :
    ¬ Factors visibleOutcome realizedOutcomeCost

def semanticSpan
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) :
    SemanticSpan SmallCarrier constantDenotation where
  holTypeCodes _context A valuation :=
    ⟨decodedHolTypeEquiv SmallCarrier constantDenotation A valuation⟩
  holTermSubstitution :=
    codedHolTerm_substitution SmallCarrier constantDenotation
  products := ⟨familiesProducts.{2}⟩
  sums := ⟨familiesSums.{2}⟩
  identity := ⟨Families.identityElimination⟩
  hierarchySubstitution := ⟨substitutionStable.{0}⟩
  hierarchyCumulative := ⟨cumulative.{0}⟩
  hierarchyProducts := ⟨piClosed.{0}⟩
  hierarchySums := ⟨sigmaClosed.{0}⟩
  hierarchyPredicative := predicativeRanks.{0}
  hierarchyNotReversible := no_reverse_cumulative.{0}
  operationalEvidenceCodes state := ⟨branchEvidenceEquiv state⟩
  operationalEvidenceNotCompletion :=
    branch_evidence_does_not_factor_through_completion
  exactEvidenceCodes depth state :=
    ⟨exactBranchEvidenceEquiv depth state⟩
  exactEvidenceNotCompletion :=
    exact_branch_evidence_does_not_factor_through_completion
  varyingUniverseNotSimple :=
    varying_code_not_a_simple_hol_type
      SmallCarrier constantDenotation
  sequentialWorkSpan := evidenceProgram_sequential_workSpan
  parallelWorkSpan := evidenceProgram_parallel_workSpan
  visibleAnswerDoesNotDetermineCost := realized_cost_not_visible_determined

/-! ## Positive and negative controls -/

theorem all_faces_share_stratified_model
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) :
    Nonempty (DependentProductBeta sharedCwf) ∧
      Nonempty (DependentSumBeta sharedCwf) ∧
      Nonempty (hierarchy.{0}.StrictlyCumulative Below) ∧
      externalFamily.{0}.PredicativeRanks ∧
      (∀ state, Nonempty
        (hierarchy.{0}.el branchEvidenceCode (ULift.up state) ≃
          exactFamily.Exact state)) :=
  ⟨(semanticSpan SmallCarrier constantDenotation).products,
    (semanticSpan SmallCarrier constantDenotation).sums,
    (semanticSpan SmallCarrier constantDenotation).hierarchyCumulative,
    (semanticSpan SmallCarrier constantDenotation).hierarchyPredicative,
    (semanticSpan SmallCarrier constantDenotation).operationalEvidenceCodes⟩

theorem shared_model_does_not_collapse_faces
    (SmallCarrier : Base → Type)
    (constantDenotation : {A : Ty Base} →
      Const A → Ty.denote.{0, 0} (liftedCarrier SmallCarrier) A) :
    (¬ Nonempty
      (FamilyFactorization completion
        (hierarchy.{0}.el branchEvidenceCode))) ∧
      (∀ depth, ¬ Nonempty
        (FamilyFactorization completion
          (hierarchy.{0}.el (exactBranchEvidenceCode depth)))) ∧
      (∀ A : Ty Base,
        ¬ (∀ point : BoolContext,
          Nonempty
            (hierarchy.{0}.el varyingCode point ≃
              AdmissibleValue
                (liftedStandardModel SmallCarrier constantDenotation) A))) ∧
      ¬ Factors visibleOutcome realizedOutcomeCost :=
  ⟨(semanticSpan SmallCarrier constantDenotation).operationalEvidenceNotCompletion,
    (semanticSpan SmallCarrier constantDenotation).exactEvidenceNotCompletion,
    (semanticSpan SmallCarrier constantDenotation).varyingUniverseNotSimple,
    (semanticSpan SmallCarrier constantDenotation).visibleAnswerDoesNotDetermineCost⟩

/-- The set-family compatibility witness validates proof irrelevance, but J
and beta also have a model with plural identity witnesses.  Therefore the
common semantic span cannot be used to select a global identity policy. -/
theorem shared_model_does_not_select_identity_policy :
    IdentityProofIrrelevance sharedCwf Families.identityFormation ∧
      (Nonempty
          (IdentityEliminationBeta (simpleFamilies.{0}.toCwf)
            ConstantMotiveCanary.identityFormation
            ConstantMotiveCanary.identityReflexivity) ∧
        ¬ IdentityProofIrrelevance (simpleFamilies.{0}.toCwf)
          ConstantMotiveCanary.identityFormation) :=
  ⟨Families.proofIrrelevance,
    ConstantMotiveCanary.elimination_does_not_force_proofIrrelevance⟩

#print axioms codedHolTerm_substitution
#print axioms branch_evidence_does_not_factor_through_completion
#print axioms exact_branch_evidence_does_not_factor_through_completion
#print axioms varying_code_not_a_simple_hol_type
#print axioms semanticSpan
#print axioms all_faces_share_stratified_model
#print axioms shared_model_does_not_collapse_faces
#print axioms shared_model_does_not_select_identity_policy

end Mettapedia.TypeTheory.StratifiedSetFamilySemanticSpan
