import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory
import Mettapedia.GSLT.Core.StructuralIsomorphism
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
import Mettapedia.OSLF.Framework.GSLTQuotientCoherence

/-!
# Agreement of generic LanguageDef semantics with established rho semantics

The generic semantic construction and the established rho GSLT both derive
their process carrier, static equations, and reduction from the exact
`rhoCalc` value.  This module proves their correspondence.  The equivalence
retains each raw pattern verbatim; only independently derived admission
witnesses are transported.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- The exact rho presentation paired with the separately admitted semantic
interpretation of reflective matching and substitution. -/
def rhoInterpretedPresentation :
    Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory.InterpretedPresentation where
  presentation := rhoInteractivePresentation
  interpretation := rhoCalcValidatedReflective.admittedReflection

/-- Rho's behavioral semantics is obtained only from its explicitly
interpreted presentation. -/
def rhoReflectiveGSLT : GSLT :=
  rhoInterpretedPresentation.toGSLTUsing defaultBasePremises

/-- The generic and established closed process carriers coincide without
changing their underlying raw patterns. -/
def presentedRhoProcessEquiv :
    rhoReflectiveGSLT.Term ≃ rhoLanguageDefGSLT.Term :=
  closedProcessEquiv

@[simp]
theorem presentedRhoProcessEquiv_pattern (term : rhoReflectiveGSLT.Term) :
    (presentedRhoProcessEquiv term).1 = term.1 :=
  rfl

/-- Exact selection of the sole equation authored by `rhoCalc`. -/
private def rhoQuoteDropEquation : Equation := rhoCalc.equations[0]

/-- Every concrete instance of rho's sole authored static equation computes
to one canonical representative. -/
private theorem rhoEquationInstanceAt_canonicalize_eq
    {fuel : Nat} {source target : Pattern}
    (equationWitness :
      EquationInstanceAt defaultBasePremises rhoCalc fuel source target) :
    Canonical.canonicalize source = Canonical.canonicalize target := by
  cases equationWitness with
  | @forward equation source target initialBindings finalBindings
      membership matched premises targetEquality =>
      have equationEquality : equation = rhoQuoteDropEquation := by
        change List.Mem equation [rhoQuoteDropEquation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      have premisesEmpty : equation.premises = [] := by
        rw [equationEquality]
        rfl
      have leftEquality : equation.left =
          .apply "NQuote" [.apply "PDrop" [.fvar "N"]] := by
        rw [equationEquality]
        rfl
      have rightEquality : equation.right = .fvar "N" := by
        rw [equationEquality]
        rfl
      rw [premisesEmpty] at premises
      cases premises
      rw [leftEquality] at matched
      rw [rightEquality] at targetEquality
      have sourceEquality := matchPattern_correct matched (by decide)
      rw [← sourceEquality, ← targetEquality]
      simp [applyBindings, Canonical.canonicalize, Canonical.canonicalizeList,
        Canonical.normalizeQuote]
  | @reverse equation source target initialBindings finalBindings
      membership matched premises targetEquality =>
      have equationEquality : equation = rhoQuoteDropEquation := by
        change List.Mem equation [rhoQuoteDropEquation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      have premisesEmpty : equation.premises = [] := by
        rw [equationEquality]
        rfl
      have leftEquality : equation.left =
          .apply "NQuote" [.apply "PDrop" [.fvar "N"]] := by
        rw [equationEquality]
        rfl
      have rightEquality : equation.right = .fvar "N" := by
        rw [equationEquality]
        rfl
      rw [premisesEmpty] at premises
      cases premises
      rw [rightEquality] at matched
      rw [leftEquality] at targetEquality
      have sourceEquality := matchPattern_correct matched (by decide)
      rw [← sourceEquality, ← targetEquality]
      simp [applyBindings, Canonical.canonicalize, Canonical.canonicalizeList,
        Canonical.normalizeQuote]

/-- Rho declares exactly one collection algebra: the parallel bag with unit
`PZero`, flattening on. -/
private theorem rhoAlgebraRule_shape
    {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra}
    (algebraRule : AlgebraRule rhoCalc rule kind algebra) :
    kind = .hashBag ∧ algebra.flatten = true ∧ algebra.unit = some "PZero" := by
  have authored := algebraRule.authored
  have declared := algebraRule.declared
  obtain ⟨parameterName, paramsEq⟩ := algebraRule.selfSorted
  simp only [rhoCalc, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [TypeExpr.bag, TypeExpr.proc, TypeExpr.baseType] at declared paramsEq
  obtain ⟨_, rfl⟩ := paramsEq
  subst declared
  exact ⟨rfl, rfl, rfl⟩

/-- Permutation of a closed parallel bag preserves the canonical
representative. -/
private theorem canonicalize_bag_perm {elements elements' : List Pattern}
    (permutation : List.Perm elements elements') :
    Canonical.canonicalize (.collection .hashBag elements none) =
      Canonical.canonicalize (.collection .hashBag elements' none) := by
  change Canonical.collapseBag
      (Canonical.normalizeBagElements (Canonical.canonicalizeList elements)) =
    Canonical.collapseBag
      (Canonical.normalizeBagElements (Canonical.canonicalizeList elements'))
  rw [Canonical.normalizeBagElements_eq_of_perm
    (Canonical.canonicalizeList_perm permutation)]

/-- A leading unit element of a closed parallel bag is absorbed by the
canonical representative. -/
private theorem canonicalize_bag_zero_cons (rest : List Pattern) :
    Canonical.canonicalize
        (.collection .hashBag (.apply "PZero" [] :: rest) none) =
      Canonical.canonicalize (.collection .hashBag rest none) := by
  change Canonical.collapseBag
      (Canonical.normalizeBagElements
        (Canonical.canonicalizeList (.apply "PZero" [] :: rest))) =
    Canonical.collapseBag
      (Canonical.normalizeBagElements (Canonical.canonicalizeList rest))
  have head : Canonical.canonicalizeList (.apply "PZero" [] :: rest) =
      .apply "PZero" [] :: Canonical.canonicalizeList rest := by
    simp [Canonical.canonicalizeList, Canonical.canonicalize]
  rw [head, Canonical.normalizeBagElements_zero_cons]

/-- Each presentation-derived law of the generic rho equation relation
preserves the established canonical representative.  Rho declares no sets, so
the set laws cannot fire; the bag laws are the canonicalizer's own
normalization steps. -/
private theorem rhoDerivedInstance_canonicalize_eq
    {source target : Pattern}
    (derived : DerivedInstance rhoCalc source target) :
    Canonical.canonicalize source = Canonical.canonicalize target := by
  cases derived with
  | bagPerm _ _ permutation =>
      exact canonicalize_bag_perm permutation
  | setPerm declaration _ _ =>
      have usesSets :=
        usesCollection_eq_true_of_collectionCarrierRule declaration
      exact absurd usesSets (by decide)
  | setDedup declaration _ =>
      have usesSets :=
        usesCollection_eq_true_of_collectionCarrierRule declaration
      exact absurd usesSets (by decide)
  | @flatten rule kind algebra pre inner post algebraRule _ _ =>
      obtain ⟨rfl, _, _⟩ := rhoAlgebraRule_shape algebraRule
      have toEnd : List.Perm (pre ++ (.collection .hashBag inner none) :: post)
          ((pre ++ post) ++ [.collection .hashBag inner none]) :=
        List.perm_middle.trans (List.perm_append_singleton _ _).symm
      have fromEnd : List.Perm ((pre ++ post) ++ inner) (pre ++ inner ++ post) := by
        rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left pre List.perm_append_comm
      rw [canonicalize_bag_perm toEnd, Canonical.canonicalize_parallel_flatten,
        canonicalize_bag_perm fromEnd]
  | singleton algebraRule _ _ =>
      obtain ⟨rfl, _, _⟩ := rhoAlgebraRule_shape algebraRule
      exact Canonical.canonicalize_parallel_singleton _
  | @unitElim rule kind algebra unit pre post algebraRule unitEq _ =>
      obtain ⟨rfl, _, unitShape⟩ := rhoAlgebraRule_shape algebraRule
      rw [unitShape] at unitEq
      cases unitEq
      have toFront : List.Perm (pre ++ (.apply "PZero" []) :: post)
          (.apply "PZero" [] :: (pre ++ post)) := List.perm_middle
      rw [canonicalize_bag_perm toFront, canonicalize_bag_zero_cons]
  | @emptyUnit rule kind algebra unit algebraRule unitEq _ =>
      obtain ⟨rfl, _, unitShape⟩ := rhoAlgebraRule_shape algebraRule
      rw [unitShape] at unitEq
      cases unitEq
      rw [Canonical.canonicalize_parallel_empty]
      simp [Canonical.canonicalize, Canonical.canonicalizeList]

/-- Each raw generator of the generic rho equation relation preserves the
established canonical representative.  The semantic setoid uses this theorem
only with closed, well-sorted endpoints. -/
theorem rhoEquationContextStep_canonicalize_eq
    {left right : Pattern}
    (generator : ReflectiveEquationContextStep rhoReflectionProfile
      defaultBasePremises rhoCalc left right) :
    Canonical.canonicalize left = Canonical.canonicalize right := by
  cases generator with
  | core coreGenerator =>
    cases coreGenerator with
    | @inContext context redex contractum equationWitness =>
      have rootCanonical :
          Canonical.canonicalize redex = Canonical.canonicalize contractum := by
        rcases equationWitness with ⟨fuel, bounded⟩ | derived
        · exact rhoEquationInstanceAt_canonicalize_eq bounded
        · exact rhoDerivedInstance_canonicalize_eq derived
      have rootReflective :
          canonicalize rhoReflectivePresentation redex =
            canonicalize rhoReflectivePresentation contractum := by
        simpa only [derivedCanonicalize_eq] using rootCanonical
      have contextual := canonicalize_fill_congr
        rhoReflectivePresentation context rootReflective
      simpa only [derivedCanonicalize_eq] using contextual
  | @reflectiveInContext context declaration reflectedLeft reflectedRight
      membership representatives =>
      have declarationEquality : declaration = rhoReflectivePresentation := by
        change List.Mem declaration [rhoReflectivePresentation] at membership
        cases membership with
        | head => rfl
        | tail _ impossible => cases impossible
      rw [declarationEquality] at representatives
      have contextual := canonicalize_fill_congr
        rhoReflectivePresentation context representatives
      simpa only [derivedCanonicalize_eq] using contextual

/-- Soundness of the typed generic rho equation closure for the established
canonical process equations. -/
theorem presentedRhoEquations_sound
    {left right : rhoReflectiveGSLT.Term}
    (equivalent : rhoReflectiveGSLT.equations.r left right) :
    rhoProcessEquations.r
      (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right) := by
  change Relation.EqvGen
    (Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory.presentedEquationGenerator
      defaultBasePremises rhoInteractivePresentation
        rhoCalcValidatedReflective.admittedReflection)
      left right at equivalent
  change Canonical.canonicalize left.1 = Canonical.canonicalize right.1
  induction equivalent with
  | rel left right generator =>
      exact rhoEquationContextStep_canonicalize_eq generator
  | refl term => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- Completeness: equality of the established canonical representatives is
already one typed reflective-equation generator at the root context. -/
theorem presentedRhoEquations_complete
    {left right : rhoReflectiveGSLT.Term}
    (equivalent : rhoProcessEquations.r
      (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right)) :
    rhoReflectiveGSLT.equations.r left right := by
  change Canonical.canonicalize left.1 =
    Canonical.canonicalize right.1 at equivalent
  have reflectiveEquality :
      canonicalize rhoReflectivePresentation left.1 =
        canonicalize rhoReflectivePresentation right.1 := by
    simpa only [derivedCanonicalize_eq] using equivalent
  have membership :
      List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
        rhoReflectionProfile.presentations := by
    change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
      [rhoReflectivePresentation.toReflectivePresentationDecl]
    exact .head _
  apply Relation.EqvGen.rel left right
  exact ReflectiveEquationContextStep.reflectiveInContext .hole membership
    reflectiveEquality

/-- The generic one-root equation semantics and the established sorted rho
equations coincide exactly under the carrier equivalence. -/
theorem presentedRhoEquations_iff
    (left right : rhoReflectiveGSLT.Term) :
    rhoReflectiveGSLT.equations.r left right ↔
      rhoProcessEquations.r
        (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right) :=
  ⟨presentedRhoEquations_sound, presentedRhoEquations_complete⟩

/-- The generic primitive step is definitionally the same least relation
compiled from `rhoCalc` as the established closed rho rewrite system. -/
theorem presentedRhoPrimitiveStep_iff
    (source target : rhoReflectiveGSLT.Term) :
    Mettapedia.GSLT.LanguageDef.ReflectiveSemanticCategory.presentedPrimitiveStep
        defaultBasePremises rhoInteractivePresentation
          rhoCalcValidatedReflective.admittedReflection source target ↔
      rhoRewriteSystem.Reduces
        (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target) :=
  Iff.rfl

/-- Soundness of the generic equation-saturated rho step under the exact
carrier equivalence. -/
theorem presentedRhoStep_sound
    {source target : rhoReflectiveGSLT.Term}
    (step : rhoReflectiveGSLT.Step source target) :
    rhoLanguageDefGSLT.Step
      (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target) := by
  obtain ⟨redex, contractum, sourceEquation, primitive, targetEquation⟩ := step
  refine ⟨presentedRhoProcessEquiv redex,
    presentedRhoProcessEquiv contractum,
    presentedRhoEquations_sound sourceEquation, ?_,
    presentedRhoEquations_sound targetEquation⟩
  exact (presentedRhoPrimitiveStep_iff redex contractum).mp primitive

/-- Completeness of the generic equation-saturated rho step under the exact
carrier equivalence. -/
theorem presentedRhoStep_complete
    {source target : rhoReflectiveGSLT.Term}
    (step : rhoLanguageDefGSLT.Step
      (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target)) :
    rhoReflectiveGSLT.Step source target := by
  obtain ⟨redex, contractum, sourceEquation, primitive, targetEquation⟩ := step
  let genericRedex : rhoReflectiveGSLT.Term :=
    presentedRhoProcessEquiv.symm redex
  let genericContractum : rhoReflectiveGSLT.Term :=
    presentedRhoProcessEquiv.symm contractum
  have sourceEquation' : rhoProcessEquations.r
      (presentedRhoProcessEquiv source)
      (presentedRhoProcessEquiv genericRedex) := by
    simpa [genericRedex] using sourceEquation
  have targetEquation' : rhoProcessEquations.r
      (presentedRhoProcessEquiv genericContractum)
      (presentedRhoProcessEquiv target) := by
    simpa [genericContractum] using targetEquation
  have primitive' : rhoRewriteSystem.Reduces
      (presentedRhoProcessEquiv genericRedex)
      (presentedRhoProcessEquiv genericContractum) := by
    simpa [genericRedex, genericContractum] using primitive
  exact ⟨genericRedex, genericContractum,
    presentedRhoEquations_complete sourceEquation',
    (presentedRhoPrimitiveStep_iff genericRedex genericContractum).mpr primitive',
    presentedRhoEquations_complete targetEquation'⟩

/-- The generic one-root rho step and the established rho GSLT step coincide
exactly under the carrier equivalence. -/
theorem presentedRhoStep_iff
    (source target : rhoReflectiveGSLT.Term) :
    rhoReflectiveGSLT.Step source target ↔
      rhoLanguageDefGSLT.Step
        (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target) :=
  ⟨presentedRhoStep_sound, presentedRhoStep_complete⟩

/-! ## Executable boundary controls transported through the exact agreement -/

/-- The closed COMM source in the generic one-root carrier. -/
def presentedClosedCommSource : rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm closedCommSource

/-- The corresponding closed COMM contractum in the generic carrier. -/
def presentedClosedCommTarget : rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm closedCommTarget

/-- Positive control: the authored COMM rule fires in the generic semantics. -/
theorem presentedClosedCommSource_step :
    rhoReflectiveGSLT.Step
      presentedClosedCommSource presentedClosedCommTarget := by
  apply presentedRhoStep_complete
  simpa [presentedClosedCommSource, presentedClosedCommTarget] using
    closedCommSource_step

/-- The closed free-Drop process in the generic carrier. -/
def presentedClosedFreeDrop : rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm closedFreeDrop

/-- Negative control: deriving the semantics from `rhoCalc` does not add an
executable free-Drop rule. -/
theorem presentedClosedFreeDrop_irreducible
    (target : rhoReflectiveGSLT.Term) :
    ¬ rhoReflectiveGSLT.Step presentedClosedFreeDrop target := by
  intro step
  apply closedFreeDrop_irreducible_in_gslt
    (presentedRhoProcessEquiv target)
  simpa [presentedClosedFreeDrop] using presentedRhoStep_sound step

/-- Negative carrier control: quotation seals a process and therefore a COMM
redex under quotation cannot inhabit the interacting process fiber. -/
theorem presentedQuotedComm_not_process :
    ¬∃ term : rhoReflectiveGSLT.Term, term.1 = commUnderQuote := by
  rintro ⟨term, termPattern⟩
  apply quotedComm_not_process
  rw [← termPattern]
  exact (presentedRhoProcessEquiv term).2

/-- Negative carrier control: the pure rho root authors no finite-set
process constructor, so generic semantics cannot acquire set-context descent. -/
theorem presentedFiniteSetContext_not_process :
    ¬∃ term : rhoReflectiveGSLT.Term, term.1 = commUnderSet := by
  rintro ⟨term, termPattern⟩
  apply finiteSet_context_not_process
  rw [← termPattern]
  exact (presentedRhoProcessEquiv term).2

/-- Map a finite generic rho rewrite path to the established rho GSLT without
changing any raw process representative. -/
def mapPresentedRhoRewritePath
    {source target : rhoReflectiveGSLT.Term} :
    rhoReflectiveGSLT.RewritePath source target →
      rhoLanguageDefGSLT.RewritePath
        (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target)
  | .nil term => .nil (presentedRhoProcessEquiv term)
  | .cons step rest =>
      .cons (presentedRhoStep_sound step) (mapPresentedRhoRewritePath rest)

/-- Map an established rho rewrite path back to the generic one-root
semantics. -/
def mapEstablishedRhoRewritePath
    {source target : rhoLanguageDefGSLT.Term} :
    rhoLanguageDefGSLT.RewritePath source target →
      rhoReflectiveGSLT.RewritePath
        (presentedRhoProcessEquiv.symm source)
        (presentedRhoProcessEquiv.symm target)
  | .nil term => .nil (presentedRhoProcessEquiv.symm term)
  | .cons step rest =>
      .cons (presentedRhoStep_complete (by simpa using step))
        (mapEstablishedRhoRewritePath rest)

@[simp]
theorem mapPresentedRhoRewritePath_length
    {source target : rhoReflectiveGSLT.Term}
    (path : rhoReflectiveGSLT.RewritePath source target) :
    (mapPresentedRhoRewritePath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [mapPresentedRhoRewritePath, GSLT.RewritePath.length,
        inductionHypothesis]

@[simp]
theorem mapEstablishedRhoRewritePath_length
    {source target : rhoLanguageDefGSLT.Term}
    (path : rhoLanguageDefGSLT.RewritePath source target) :
    (mapEstablishedRhoRewritePath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [mapEstablishedRhoRewritePath, GSLT.RewritePath.length,
        inductionHypothesis]

/-- Reflexive-transitive reduction also coincides exactly under the carrier
equivalence. -/
theorem presentedRhoMultiStep_iff
    (source target : rhoReflectiveGSLT.Term) :
    rhoReflectiveGSLT.MultiStep source target ↔
      rhoLanguageDefGSLT.MultiStep
        (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target) := by
  constructor
  · intro path
    induction path with
    | refl term => exact .refl _
    | step first rest inductionHypothesis =>
        exact .step (presentedRhoStep_sound first) inductionHypothesis
  · intro path
    have lift : ∀ {left right : rhoLanguageDefGSLT.Term},
        rhoLanguageDefGSLT.MultiStep left right →
          rhoReflectiveGSLT.MultiStep
            (presentedRhoProcessEquiv.symm left)
            (presentedRhoProcessEquiv.symm right) := by
      intro left right derivation
      induction derivation with
      | refl term => exact .refl _
      | step first rest inductionHypothesis =>
          exact .step
            (presentedRhoStep_complete (by simpa using first))
            inductionHypothesis
    simpa using lift path

/-- Strong bisimilarity is transported from the generic semantics to the
established rho semantics by exact one-step correspondence. -/
theorem presentedRhoBisimilar_sound
    {left right : rhoReflectiveGSLT.Term}
    (equivalent : rhoReflectiveGSLT.Bisimilar left right) :
    rhoLanguageDefGSLT.Bisimilar
      (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right) :=
  GSLT.bisimilar_map_of_step_iff presentedRhoProcessEquiv
    presentedRhoStep_iff equivalent

/-- The inverse carrier equivalence also preserves bisimilarity. -/
theorem establishedRhoBisimilar_to_presented
    {left right : rhoLanguageDefGSLT.Term}
    (equivalent : rhoLanguageDefGSLT.Bisimilar left right) :
    rhoReflectiveGSLT.Bisimilar
      (presentedRhoProcessEquiv.symm left)
      (presentedRhoProcessEquiv.symm right) := by
  apply GSLT.bisimilar_map_of_step_iff presentedRhoProcessEquiv.symm
    (source := rhoLanguageDefGSLT) (target := rhoReflectiveGSLT) ?_ equivalent
  intro source target
  simpa using
    (presentedRhoStep_iff
      (presentedRhoProcessEquiv.symm source)
      (presentedRhoProcessEquiv.symm target)).symm

/-- The interpreted presentation and the established rho semantics are
structurally isomorphic: the carrier bijection preserves and reflects static
equations and one-step behavior separately.  This stronger boundary is what
permits executable semantic structure to transport between the two views. -/
def rhoStructuralIsomorphism :
    GSLT.StructuralIsomorphism rhoReflectiveGSLT rhoLanguageDefGSLT where
  termEquiv := presentedRhoProcessEquiv
  equiv_iff := by
    intro left right
    exact (presentedRhoEquations_iff left right).symm
  step_iff := by
    intro source target
    exact (presentedRhoStep_iff source target).symm

/-- The behavioral GSLT derived generically from `rhoCalc` is isomorphic to
the established sorted rho GSLT. -/
def rhoSemanticIso : rhoReflectiveGSLT ≅ rhoLanguageDefGSLT where
  hom :=
    { toFun := presentedRhoProcessEquiv
      preserves_bisim := presentedRhoBisimilar_sound }
  inv :=
    { toFun := presentedRhoProcessEquiv.symm
      preserves_bisim := establishedRhoBisimilar_to_presented }
  hom_inv_id := by
    apply GSLT.Morphism.ext
    funext term
    exact presentedRhoProcessEquiv.left_inv term
  inv_hom_id := by
    apply GSLT.Morphism.ext
    funext term
    exact presentedRhoProcessEquiv.right_inv term

/-! ## OSLF equation-quotient canaries

These examples exercise the sole OSLF construction on the rho calculus.  The
negative example is intentionally a syntax predicate rather than an alternate
OSLF: it demonstrates why an equation-sensitive predicate is rejected at the
semantic boundary. -/

/-- The closed inert process transported into the generic LanguageDef-derived
rho carrier. -/
def presentedClosedNil : rhoReflectiveGSLT.Term :=
  presentedRhoProcessEquiv.symm closedNil

/-- The singleton parallel contractum and the inert process are genuinely
different authored presentations. -/
theorem presentedClosedCommTarget_ne_presentedClosedNil :
    presentedClosedCommTarget ≠ presentedClosedNil := by
  intro equal
  have mapped := congrArg presentedRhoProcessEquiv equal
  rw [presentedClosedCommTarget, presentedClosedNil] at mapped
  simp only [Equiv.apply_symm_apply] at mapped
  have patternEqual := congrArg Subtype.val mapped
  simp [closedCommTarget, closedNil] at patternEqual

/-- The two distinct presentations belong to the same rho equation class. -/
theorem presentedClosedCommTarget_equivalent_presentedClosedNil :
    rhoReflectiveGSLT.Equiv presentedClosedCommTarget presentedClosedNil := by
  apply presentedRhoEquations_complete
  simpa [presentedClosedCommTarget, presentedClosedNil] using
    closedParallelSingleton_equivalent_nil

/-- A presentation-sensitive singleton observation used only as a rejection
canary. -/
def rawCommTargetSingleton : rhoReflectiveGSLT.Term → Prop :=
  fun term => term = presentedClosedCommTarget

/-- The syntax predicate distinguishes two presentations of one process. -/
theorem rawSyntaxPredicate_distinguishes_equivalent_presentations :
    rawCommTargetSingleton presentedClosedCommTarget ∧
      ¬rawCommTargetSingleton presentedClosedNil := by
  constructor
  · rfl
  · intro equal
    exact presentedClosedCommTarget_ne_presentedClosedNil equal.symm

/-- The presentation-sensitive singleton cannot enter OSLF's semantic
predicate carrier. -/
theorem rawCommTargetSingleton_not_equationInvariant :
    ¬EquationInvariant rhoReflectiveGSLT rawCommTargetSingleton := by
  intro invariant
  have transported :=
    (invariant presentedClosedCommTarget_equivalent_presentedClosedNil).mp rfl
  exact presentedClosedCommTarget_ne_presentedClosedNil transported.symm

/-- Every predicate admitted by OSLF gives the same answer on equivalent rho
presentations. -/
theorem gsltOSLF_cannot_distinguish_presentations
    (predicate : EquationPredicate rhoReflectiveGSLT) :
    (gsltOSLF rhoReflectiveGSLT).satisfies (S := ())
        presentedClosedCommTarget predicate ↔
      (gsltOSLF rhoReflectiveGSLT).satisfies (S := ())
        presentedClosedNil predicate :=
  predicate.2 presentedClosedCommTarget_equivalent_presentedClosedNil

/-- Positive operational canary: authored communication remains a diamond
step in rho's equation-respecting OSLF. -/
theorem gsltOSLF_sees_communication :
    (gsltOSLF rhoReflectiveGSLT).satisfies (S := ())
      presentedClosedCommSource
      (exactTargetNativeType rhoReflectiveGSLT
        presentedClosedCommTarget).pred :=
  (satisfies_exactTargetNativeType_iff_step rhoReflectiveGSLT _ _).2
    presentedClosedCommSource_step

/-- Negative operational canary: equation saturation does not invent a
rewrite from a free `Drop`. -/
theorem gsltOSLF_keeps_freeDrop_inert :
    ¬(gsltOSLF rhoReflectiveGSLT).satisfies (S := ())
      presentedClosedFreeDrop
      (semanticDiamond rhoReflectiveGSLT
        (saturatePredicate rhoReflectiveGSLT (fun _ => True))) := by
  intro possible
  change gsltDiamond rhoReflectiveGSLT
    (saturatePredicate rhoReflectiveGSLT (fun _ => True)).1
    presentedClosedFreeDrop at possible
  obtain ⟨target, step, _⟩ :=
    (gsltDiamond_spec rhoReflectiveGSLT _ _).mp possible
  exact presentedClosedFreeDrop_irreducible target step

#print axioms presentedClosedCommTarget_ne_presentedClosedNil
#print axioms presentedClosedCommTarget_equivalent_presentedClosedNil
#print axioms rawSyntaxPredicate_distinguishes_equivalent_presentations
#print axioms rawCommTargetSingleton_not_equationInvariant
#print axioms gsltOSLF_cannot_distinguish_presentations
#print axioms gsltOSLF_sees_communication
#print axioms gsltOSLF_keeps_freeDrop_inert
#print axioms rhoStructuralIsomorphism

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
