import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerInstance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-!
# Finitely many successor classes, and adequacy for rho

The step modulo equations of the established rho GSLT reaches every
spelling of every successor, so a closed process has unboundedly many
successor representatives.  By the completeness of the canonical stepper it
has finitely many successor classes: every saturated step lands in the class
of a depth-one successor of the canonical representative, and those form a
list.  This discharges the image-finiteness hypothesis of the generic
Hennessy–Milner theorem, so adequacy holds for rho unconditionally, under any
observation set of equation-invariant predicates.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.EffectiveStructure
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerInstance

set_option autoImplicit false

/-- Rho's proved canonical section is an exact executable normalizer for the
semantic equation relation: it stays in the same class, and equality of its
outputs characterizes that class exactly. -/
def rhoCanonicalEquationNormalizer :
    CanonicalEquationNormalizer rhoLanguageDefGSLT where
  normalize := RhoClosedTerm.canonicalize
  sound := by
    intro term
    change canonicalize term.1 = canonicalize (canonicalize term.1)
    exact (canonicalize_idempotent term.1).symm
  complete := by
    intro left right
    change rhoProcessEquations.r left right ↔
      left.canonicalize = right.canonicalize
    constructor
    · exact canonicalize_eq_of_rhoProcessEquations
    · intro equality
      exact congrArg Subtype.val equality

/-- The executable depth-one successors of a closed process's canonical
representative.  Each result is accompanied by the derived closed-process
witness; proof erasure leaves exactly the finite `rewriteAt` list. -/
def canonicalSuccessorList (term : RhoProcess) : List RhoProcess :=
  let source := term.canonicalize
  let successors := rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1
    source.1
  successors.pmap
    (fun _ step => source.stepTarget step)
    (by
      intro target member
      exact ⟨1, mem_rewriteAt_iff_stepAt.mp member⟩)

/-- Membership in the typed runtime list exposes membership in the raw
generated stepper list. -/
theorem pattern_mem_of_mem_canonicalSuccessorList
    {source target : RhoProcess}
    (member : target ∈ canonicalSuccessorList source) :
    target.1 ∈ rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1
      (canonicalize source.1) := by
  simp only [canonicalSuccessorList, List.mem_pmap] at member
  obtain ⟨pattern, patternMember, equality⟩ := member
  have patternEquality := congrArg Subtype.val equality
  change pattern = target.1 at patternEquality
  rwa [← patternEquality]

/-- Every enumerated canonical successor is a genuine modulo-equations
rho step from the authored input representative. -/
theorem canonicalSuccessorList_sound
    {source target : RhoProcess}
    (member : target ∈ canonicalSuccessorList source) :
    rhoLanguageDefGSLT.Step source target := by
  have rawMember := pattern_mem_of_mem_canonicalSuccessorList member
  have canonicalStep : RhoStepAt 1 (canonicalize source.1) target.1 :=
    mem_rewriteAt_iff_stepAt.mp rawMember
  refine ⟨source.canonicalize, target, ?_, ⟨1, canonicalStep⟩, rfl⟩
  change canonicalize source.1 = canonicalize (canonicalize source.1)
  exact (canonicalize_idempotent source.1).symm

/-- Every saturated step from a closed process lands in the class of an
entry of the executable canonical-successor list. -/
theorem canonicalSuccessorList_complete (term : RhoProcess) :
    ∀ ⦃target : RhoProcess⦄, rhoLanguageDefGSLT.Step term target →
      ∃ representative ∈ canonicalSuccessorList term,
        rhoLanguageDefGSLT.Equiv target representative := by
  intro target step
  obtain ⟨redex, contractum, termRedex, reduces, contractumTarget⟩ := step
  have termRedexEq : canonicalize term.1 = canonicalize redex.1 := termRedex
  have contractumTargetEq : canonicalize contractum.1 = canonicalize target.1 := contractumTarget
  have redexClosed := (rhoClosedTermWellSorted_process_iff redex.1).mp redex.2
  have termClosed := (rhoClosedTermWellSorted_process_iff term.1).mp term.2
  obtain ⟨target', canonicalStep, targetEq⟩ :=
    canonicalStep_complete_of_rhoStep redexClosed.1 redexClosed.2 reduces
  rw [← termRedexEq] at canonicalStep
  have closed := rhoStepAt_preserves_closed
    (canonicalize_procWellSorted [] termClosed.1)
    (canonicalize_binderSafeAt term.1 0 termClosed.2) canonicalStep
  let representative : RhoProcess :=
    ⟨target', (rhoClosedTermWellSorted_process_iff target').mpr closed⟩
  refine ⟨representative, ?_, ?_⟩
  · simp only [canonicalSuccessorList, List.mem_pmap]
    refine ⟨target', mem_rewriteAt_iff_stepAt.mpr canonicalStep, ?_⟩
    apply Subtype.ext
    rfl
  · show canonicalize target.1 = canonicalize target'
    rw [targetEq]
    exact contractumTargetEq.symm

/-- The executable rho stepper enumerates exactly the semantic successor
classes: no listed edge is spurious, and no `E;R;E` edge is missed modulo
`E`. -/
def rhoSuccessorClassEnumeration :
    SuccessorClassEnumeration rhoLanguageDefGSLT where
  successors := canonicalSuccessorList
  sound := by
    intro source target member
    exact canonicalSuccessorList_sound member
  complete := by
    intro source target step
    exact canonicalSuccessorList_complete source step

/-- Rho's proved canonicalizer and finite class enumerator, packaged as the
endpoint-level runtime contract of the established semantic GSLT. -/
def rhoQuotientEndpointRuntime :
    QuotientEndpointRuntime rhoLanguageDefGSLT where
  equationNormalizer := rhoCanonicalEquationNormalizer
  successorClasses := rhoSuccessorClassEnumeration

/-! ## The effective structure on the public interpreted presentation -/

/-- The endpoint runtime transported to the exact GSLT used by the public
rho OSLF. -/
def presentedRhoQuotientEndpointRuntime :
    QuotientEndpointRuntime rhoReflectiveGSLT :=
  QuotientEndpointRuntime.transport rhoStructuralIsomorphism
    rhoQuotientEndpointRuntime

/-- The canonical equation normalizer transported to the exact GSLT used by
the public rho OSLF.  Thus equation decision and modal interpretation share
one semantic object rather than merely agreeing after an external comparison. -/
def presentedRhoCanonicalEquationNormalizer :
    CanonicalEquationNormalizer rhoReflectiveGSLT :=
  presentedRhoQuotientEndpointRuntime.equationNormalizer

/-- The finite successor-class enumerator transported to the exact GSLT used
by the public rho OSLF. -/
def presentedRhoSuccessorClassEnumeration :
    SuccessorClassEnumeration rhoReflectiveGSLT :=
  presentedRhoQuotientEndpointRuntime.successorClasses

/-- The public interpreted rho presentation has an executable list whose
quotient image is exactly its semantic one-step relation, for every pair of
authored representatives. -/
theorem presentedRhoSuccessorClasses_exact
    (source target : rhoReflectiveGSLT.Term) :
    Quotient.mk rhoReflectiveGSLT.equations target ∈
        presentedRhoSuccessorClassEnumeration.quotientSuccessorsAt source ↔
      SemanticStep rhoReflectiveGSLT
        (Quotient.mk rhoReflectiveGSLT.equations source)
        (Quotient.mk rhoReflectiveGSLT.equations target) :=
  SuccessorClassEnumeration.mem_quotientSuccessorsAt_iff_semanticStep
    presentedRhoSuccessorClassEnumeration source target

/-- Normalizing an arbitrary public rho representative and then enumerating
finite successor classes is exact for the same quotient transition relation
that generates the public OSLF modalities. -/
theorem presentedRhoNormalizedSuccessorClasses_exact
    (source target : rhoReflectiveGSLT.Term) :
    Quotient.mk rhoReflectiveGSLT.equations target ∈
        presentedRhoQuotientEndpointRuntime.normalizedSuccessorClassesAt source ↔
      SemanticStep rhoReflectiveGSLT
        (Quotient.mk rhoReflectiveGSLT.equations source)
        (Quotient.mk rhoReflectiveGSLT.equations target) :=
  QuotientEndpointRuntime.mem_normalizedSuccessorClassesAt_iff_semanticStep
    presentedRhoQuotientEndpointRuntime source target

/-- The executable list is exact after projecting its entries to rho's
semantic equation classes. -/
theorem canonicalSuccessorClasses_exact (source target : RhoProcess) :
    Quotient.mk rhoLanguageDefGSLT.equations target ∈
        rhoSuccessorClassEnumeration.quotientSuccessorsAt source ↔
      SemanticStep rhoLanguageDefGSLT
        (Quotient.mk rhoLanguageDefGSLT.equations source)
        (Quotient.mk rhoLanguageDefGSLT.equations target) :=
  SuccessorClassEnumeration.mem_quotientSuccessorsAt_iff_semanticStep
    rhoSuccessorClassEnumeration source target

/-! ## Executable positive and negative controls -/

/-- The generated COMM edge makes the executable successor list nonempty. -/
theorem canonicalSuccessorList_closedComm_nonempty :
    ∃ representative, representative ∈ canonicalSuccessorList closedCommSource := by
  have step : rhoLanguageDefGSLT.Step closedCommSource closedCommTarget :=
    rhoRewriteSystem_reduces_to_gsltStep
      closedCommSource_reduces_closedCommTarget
  obtain ⟨representative, member, _⟩ :=
    canonicalSuccessorList_complete closedCommSource step
  exact ⟨representative, member⟩

/-- The pure free-drop control has no generated successors. -/
theorem canonicalSuccessorList_closedFreeDrop_nil :
    canonicalSuccessorList closedFreeDrop = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro target member
  exact closedFreeDrop_irreducible_in_gslt target
    (canonicalSuccessorList_sound member)

/-- The finite set view used by Hennessy–Milner adequacy is derived from the
executable list rather than postulated independently. -/
def canonicalSuccessors (term : RhoProcess) : Set RhoProcess :=
  { target | target ∈ canonicalSuccessorList term }

theorem canonicalSuccessors_finite (term : RhoProcess) :
    (canonicalSuccessors term).Finite :=
  List.finite_toSet _

/-- Set-level class coverage is the extensional view of the executable
enumerator. -/
theorem step_covered (term : RhoProcess) :
    ∀ ⦃target : RhoProcess⦄, rhoLanguageDefGSLT.Step term target →
      ∃ representative ∈ canonicalSuccessors term,
        rhoLanguageDefGSLT.Equiv target representative := by
  intro target step
  obtain ⟨representative, member, equivalent⟩ :=
    rhoSuccessorClassEnumeration.complete term target step
  refine ⟨representative, ?_, equivalent⟩
  exact member

/-- The established rho GSLT is image-finite modulo its equations under every
observation set. -/
theorem rho_imageFiniteModulo (Atom : Type) (observe : Atom → EquationPredicate rhoLanguageDefGSLT) :
    (rhoSystem Atom observe).ImageFiniteModulo := by
  intro _ term
  exact ⟨canonicalSuccessors term, canonicalSuccessors_finite term, step_covered term⟩

/-- Hennessy–Milner adequacy for rho, unconditionally: logical equivalence
under any equation-invariant observation set is bisimilarity. -/
theorem logicallyEquivalent_iff_bisimilar (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) (left right : RhoProcess) :
    (rhoSystem Atom observe).LogicallyEquivalent left right ↔
      (rhoSystem Atom observe).Bisimilar left right :=
  HennessyMilnerInstance.logicallyEquivalent_iff_bisimilar Atom observe
    (rho_imageFiniteModulo Atom observe) left right

/-- The negation-free fragment for rho: the logical preorder is the simulation
preorder. -/
theorem logicalPreorder_iff_similar (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) (left right : RhoProcess) :
    (rhoSystem Atom observe).LogicalPreorder left right ↔
      (rhoSystem Atom observe).Similar left right :=
  HennessyMilnerInstance.logicalPreorder_iff_similar Atom observe
    (rho_imageFiniteModulo Atom observe) left right

/-- Adequacy on rho's equation classes. -/
theorem logicallyEquivalentClass_iff_bisimilarClass (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    (left right : Quotient rhoLanguageDefGSLT.equations) :
    (rhoSystem Atom observe).logicallyEquivalentClass left right ↔
      (rhoSystem Atom observe).bisimilarClass left right :=
  HennessyMilnerInstance.logicallyEquivalentClass_iff_bisimilarClass Atom observe
    (rho_imageFiniteModulo Atom observe) left right

#print axioms rhoCanonicalEquationNormalizer
#print axioms rhoQuotientEndpointRuntime
#print axioms presentedRhoQuotientEndpointRuntime
#print axioms presentedRhoCanonicalEquationNormalizer
#print axioms presentedRhoSuccessorClassEnumeration
#print axioms presentedRhoSuccessorClasses_exact
#print axioms presentedRhoNormalizedSuccessorClasses_exact
#print axioms canonicalSuccessorList_sound
#print axioms canonicalSuccessorList_complete
#print axioms canonicalSuccessorClasses_exact
#print axioms canonicalSuccessorList_closedComm_nonempty
#print axioms canonicalSuccessorList_closedFreeDrop_nil
#print axioms rho_imageFiniteModulo

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho
