import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ClosedCarrierAgreement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

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

/-- The generic and established closed process carriers coincide without
changing their underlying raw patterns. -/
def presentedRhoProcessEquiv :
    rhoIGSLT.toGSLT.Term ≃ rhoLanguageDefGSLT.Term :=
  closedProcessEquiv

@[simp]
theorem presentedRhoProcessEquiv_pattern (term : rhoIGSLT.toGSLT.Term) :
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

/-- Each raw generator of the generic rho equation relation preserves the
established canonical representative.  The semantic setoid uses this theorem
only with closed, well-sorted endpoints. -/
theorem rhoEquationContextStep_canonicalize_eq
    {left right : Pattern}
    (generator : EquationContextStep defaultBasePremises rhoCalc left right) :
    Canonical.canonicalize left = Canonical.canonicalize right := by
  cases generator with
  | @inContext context redex contractum equationWitness =>
      obtain ⟨fuel, bounded⟩ := equationWitness
      have rootCanonical := rhoEquationInstanceAt_canonicalize_eq bounded
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
    {left right : rhoIGSLT.toGSLT.Term}
    (equivalent : rhoIGSLT.toGSLT.equations.r left right) :
    rhoProcessEquations.r
      (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right) := by
  change Relation.EqvGen
    (presentedEquationGenerator defaultBasePremises rhoInteractivePresentation)
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
    {left right : rhoIGSLT.toGSLT.Term}
    (equivalent : rhoProcessEquations.r
      (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right)) :
    rhoIGSLT.toGSLT.equations.r left right := by
  change Canonical.canonicalize left.1 =
    Canonical.canonicalize right.1 at equivalent
  have reflectiveEquality :
      canonicalize rhoReflectivePresentation left.1 =
        canonicalize rhoReflectivePresentation right.1 := by
    simpa only [derivedCanonicalize_eq] using equivalent
  have membership :
      List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
        rhoCalc.reflectivePresentations := by
    change List.Mem rhoReflectivePresentation.toReflectivePresentationDecl
      [rhoReflectivePresentation.toReflectivePresentationDecl]
    exact .head _
  apply Relation.EqvGen.rel left right
  exact EquationContextStep.reflectiveInContext .hole membership
    reflectiveEquality

/-- The generic one-root equation semantics and the established sorted rho
equations coincide exactly under the carrier equivalence. -/
theorem presentedRhoEquations_iff
    (left right : rhoIGSLT.toGSLT.Term) :
    rhoIGSLT.toGSLT.equations.r left right ↔
      rhoProcessEquations.r
        (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right) :=
  ⟨presentedRhoEquations_sound, presentedRhoEquations_complete⟩

/-- The generic primitive step is definitionally the same least relation
compiled from `rhoCalc` as the established closed rho rewrite system. -/
theorem presentedRhoPrimitiveStep_iff
    (source target : rhoIGSLT.toGSLT.Term) :
    presentedPrimitiveStep defaultBasePremises rhoInteractivePresentation
        source target ↔
      rhoRewriteSystem.Reduces
        (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target) :=
  Iff.rfl

/-- Soundness of the generic equation-saturated rho step under the exact
carrier equivalence. -/
theorem presentedRhoStep_sound
    {source target : rhoIGSLT.toGSLT.Term}
    (step : rhoIGSLT.toGSLT.Step source target) :
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
    {source target : rhoIGSLT.toGSLT.Term}
    (step : rhoLanguageDefGSLT.Step
      (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target)) :
    rhoIGSLT.toGSLT.Step source target := by
  obtain ⟨redex, contractum, sourceEquation, primitive, targetEquation⟩ := step
  let genericRedex : rhoIGSLT.toGSLT.Term :=
    presentedRhoProcessEquiv.symm redex
  let genericContractum : rhoIGSLT.toGSLT.Term :=
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
    (source target : rhoIGSLT.toGSLT.Term) :
    rhoIGSLT.toGSLT.Step source target ↔
      rhoLanguageDefGSLT.Step
        (presentedRhoProcessEquiv source) (presentedRhoProcessEquiv target) :=
  ⟨presentedRhoStep_sound, presentedRhoStep_complete⟩

/-! ## Executable boundary controls transported through the exact agreement -/

/-- The closed COMM source in the generic one-root carrier. -/
def presentedClosedCommSource : rhoIGSLT.toGSLT.Term :=
  presentedRhoProcessEquiv.symm closedCommSource

/-- The corresponding closed COMM contractum in the generic carrier. -/
def presentedClosedCommTarget : rhoIGSLT.toGSLT.Term :=
  presentedRhoProcessEquiv.symm closedCommTarget

/-- Positive control: the authored COMM rule fires in the generic semantics. -/
theorem presentedClosedCommSource_step :
    rhoIGSLT.toGSLT.Step
      presentedClosedCommSource presentedClosedCommTarget := by
  apply presentedRhoStep_complete
  simpa [presentedClosedCommSource, presentedClosedCommTarget] using
    closedCommSource_step

/-- The closed free-Drop process in the generic carrier. -/
def presentedClosedFreeDrop : rhoIGSLT.toGSLT.Term :=
  presentedRhoProcessEquiv.symm closedFreeDrop

/-- Negative control: deriving the semantics from `rhoCalc` does not add an
executable free-Drop rule. -/
theorem presentedClosedFreeDrop_irreducible
    (target : rhoIGSLT.toGSLT.Term) :
    ¬ rhoIGSLT.toGSLT.Step presentedClosedFreeDrop target := by
  intro step
  apply closedFreeDrop_irreducible_in_gslt
    (presentedRhoProcessEquiv target)
  simpa [presentedClosedFreeDrop] using presentedRhoStep_sound step

/-- Negative carrier control: quotation seals a process and therefore a COMM
redex under quotation cannot inhabit the interacting process fiber. -/
theorem presentedQuotedComm_not_process :
    ¬∃ term : rhoIGSLT.toGSLT.Term, term.1 = commUnderQuote := by
  rintro ⟨term, termPattern⟩
  apply quotedComm_not_process
  rw [← termPattern]
  exact (presentedRhoProcessEquiv term).2

/-- Negative carrier control: the pure rho root authors no finite-set
process constructor, so generic semantics cannot acquire set-context descent. -/
theorem presentedFiniteSetContext_not_process :
    ¬∃ term : rhoIGSLT.toGSLT.Term, term.1 = commUnderSet := by
  rintro ⟨term, termPattern⟩
  apply finiteSet_context_not_process
  rw [← termPattern]
  exact (presentedRhoProcessEquiv term).2

/-- Map a finite generic rho rewrite path to the established rho GSLT without
changing any raw process representative. -/
def mapPresentedRhoRewritePath
    {source target : rhoIGSLT.toGSLT.Term} :
    rhoIGSLT.toGSLT.RewritePath source target →
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
      rhoIGSLT.toGSLT.RewritePath
        (presentedRhoProcessEquiv.symm source)
        (presentedRhoProcessEquiv.symm target)
  | .nil term => .nil (presentedRhoProcessEquiv.symm term)
  | .cons step rest =>
      .cons (presentedRhoStep_complete (by simpa using step))
        (mapEstablishedRhoRewritePath rest)

@[simp]
theorem mapPresentedRhoRewritePath_length
    {source target : rhoIGSLT.toGSLT.Term}
    (path : rhoIGSLT.toGSLT.RewritePath source target) :
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
    (source target : rhoIGSLT.toGSLT.Term) :
    rhoIGSLT.toGSLT.MultiStep source target ↔
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
          rhoIGSLT.toGSLT.MultiStep
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
    {left right : rhoIGSLT.toGSLT.Term}
    (equivalent : rhoIGSLT.toGSLT.Bisimilar left right) :
    rhoLanguageDefGSLT.Bisimilar
      (presentedRhoProcessEquiv left) (presentedRhoProcessEquiv right) :=
  GSLT.bisimilar_map_of_step_iff presentedRhoProcessEquiv
    presentedRhoStep_iff equivalent

/-- The inverse carrier equivalence also preserves bisimilarity. -/
theorem establishedRhoBisimilar_to_presented
    {left right : rhoLanguageDefGSLT.Term}
    (equivalent : rhoLanguageDefGSLT.Bisimilar left right) :
    rhoIGSLT.toGSLT.Bisimilar
      (presentedRhoProcessEquiv.symm left)
      (presentedRhoProcessEquiv.symm right) := by
  apply GSLT.bisimilar_map_of_step_iff presentedRhoProcessEquiv.symm
    (source := rhoLanguageDefGSLT) (target := rhoIGSLT.toGSLT) ?_ equivalent
  intro source target
  simpa using
    (presentedRhoStep_iff
      (presentedRhoProcessEquiv.symm source)
      (presentedRhoProcessEquiv.symm target)).symm

/-- The behavioral GSLT derived generically from `rhoCalc` is isomorphic to
the established sorted rho GSLT. -/
def rhoSemanticIso : rhoIGSLT.toGSLT ≅ rhoLanguageDefGSLT where
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

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
