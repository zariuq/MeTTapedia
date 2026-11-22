import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho
import Mettapedia.OSLF.Framework.EnumeratedAdequacy

/-!
# Parallel partners as labels: context adequacy for rho

A rho process interacts with its environment only through parallel
composition, so the contexts that can enable a step are the parallel
partners.  Labeling steps by partners turns the established rho GSLT into a
labeled system: the label `Q` steps from `P` to `P'` when `P | Q` steps to
`P'`.  Because the equations are computed by the canonical section, plugging
respects them, and because the canonical stepper is complete, every partner
system is image-finite modulo the equations.  Partner-labeled
Hennessy–Milner equivalence is therefore partner bisimilarity,
unconditionally, and every partner formula is a native type of the sole
generated OSLF.

The module ends with the canary that shows why the labels are needed: a
waiting input and the inert process are reduction-bisimilar, and one parallel
partner separates them.  The box-free OSLF fragment over the public rho
presentation is also shown adequate for forward bisimilarity, again
unconditionally.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.EffectiveStructure
open Mettapedia.OSLF.Framework.EnumeratedAdequacy
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
open Mettapedia.OSLF.Formula.Adequacy
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
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
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HennessyMilnerRho

set_option autoImplicit false

/-! ## Closed parallel composition -/

/-- The parallel composition of two closed processes is a closed process. -/
def par (left right : RhoProcess) : RhoProcess :=
  ⟨.collection .hashBag [left.1, right.1] none, by
    have leftClosed := (rhoClosedTermWellSorted_process_iff left.1).mp left.2
    have rightClosed := (rhoClosedTermWellSorted_process_iff right.1).mp right.2
    refine (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (.cons leftClosed.1 (.cons rightClosed.1 .nil)), ?_⟩
    simp [binderSafeAt, binderSafeListAt, leftClosed.2, rightClosed.2]⟩

@[simp]
theorem par_pattern (left right : RhoProcess) :
    (par left right).1 = .collection .hashBag [left.1, right.1] none :=
  rfl

/-- Plugging into a parallel partner respects the equations. -/
theorem par_equiv_left {left left' : RhoProcess} (right : RhoProcess)
    (equivalent : rhoLanguageDefGSLT.Equiv left left') :
    rhoLanguageDefGSLT.Equiv (par left right) (par left' right) := by
  change canonicalize (.collection .hashBag [left.1, right.1] none) =
    canonicalize (.collection .hashBag [left'.1, right.1] none)
  exact canonicalize_bag_cons_congr equivalent (List.Perm.refl _)

/-- The inert partner is absorbed by the equations. -/
theorem par_nil_equiv (process : RhoProcess) :
    rhoLanguageDefGSLT.Equiv (par process closedNil) process := by
  change canonicalize (.collection .hashBag [process.1, .apply "PZero" []] none) =
    canonicalize process.1
  rw [canonicalize_bag_cons_congr (head' := process.1) (tail' := []) rfl ?_,
    canonicalize_parallel_singleton]
  have zero : canonicalize (.apply "PZero" []) = .apply "PZero" [] := rfl
  simp only [List.map_cons, List.map_nil, zero, bagContents_zero_cons]
  exact List.Perm.refl _

/-! ## The partner-labeled system -/

/-- The established rho GSLT with parallel partners as labels and an
equation-invariant observation set. -/
def partnerSystem (Atom : Type) (observe : Atom → EquationPredicate rhoLanguageDefGSLT) :
    System.{0, 0} rhoLanguageDefGSLT where
  Atom := Atom
  observes := fun atom => (observe atom).1
  observes_resp := fun atom _ _ equivalent => (observe atom).2 equivalent
  Label := RhoProcess
  act := fun partner source target => rhoLanguageDefGSLT.Step (par source partner) target
  act_resp_left := by
    intro partner left right target equivalent step
    exact rhoLanguageDefGSLT.rewrites_resp_left (par_equiv_left partner equivalent) step
  act_resp_right := by
    intro partner source target target' step equivalent
    exact rhoLanguageDefGSLT.rewrites_resp_right step equivalent

/-- Every partner system has finitely many successor classes, by the
completeness of the canonical stepper. -/
theorem partnerSystem_imageFiniteModulo (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) :
    (partnerSystem Atom observe).ImageFiniteModulo :=
  imageFiniteModulo_of_enumeration _ rhoSuccessorClassEnumeration
    (fun partner source => par source partner) (fun step => step)

/-- Partner-labeled Hennessy–Milner adequacy for rho, unconditionally. -/
theorem partnerLogicallyEquivalent_iff_bisimilar (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) (left right : RhoProcess) :
    (partnerSystem Atom observe).LogicallyEquivalent left right ↔
      (partnerSystem Atom observe).Bisimilar left right :=
  (partnerSystem Atom observe).logicallyEquivalent_iff_bisimilar
    (partnerSystem_imageFiniteModulo Atom observe) left right

/-- The negation-free partner fragment characterizes partner simulation. -/
theorem partnerLogicalPreorder_iff_similar (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) (left right : RhoProcess) :
    (partnerSystem Atom observe).LogicalPreorder left right ↔
      (partnerSystem Atom observe).Similar left right :=
  (partnerSystem Atom observe).logicalPreorder_iff_similar
    (partnerSystem_imageFiniteModulo Atom observe) left right

/-- Partner adequacy on rho's equation classes. -/
theorem partnerLogicallyEquivalentClass_iff_bisimilarClass (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT)
    (left right : Quotient rhoLanguageDefGSLT.equations) :
    (partnerSystem Atom observe).logicallyEquivalentClass left right ↔
      (partnerSystem Atom observe).bisimilarClass left right :=
  (partnerSystem Atom observe).logicallyEquivalentClass_iff_bisimilarClass
    (partnerSystem_imageFiniteModulo Atom observe) left right

/-- Every partner formula is a native type of the sole generated OSLF, and
agreement on all of them is partner bisimilarity. -/
theorem partnerFormulaNativeTypes_equivalent_iff_bisimilar (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) (left right : RhoProcess) :
    (∀ formula : Formula Atom RhoProcess,
      ((gsltOSLF rhoLanguageDefGSLT).satisfies (S := ()) left
          (formulaNativeType (partnerSystem Atom observe) formula).pred ↔
       (gsltOSLF rhoLanguageDefGSLT).satisfies (S := ()) right
          (formulaNativeType (partnerSystem Atom observe) formula).pred)) ↔
      (partnerSystem Atom observe).Bisimilar left right :=
  formulaNativeTypes_equivalent_iff_bisimilar (partnerSystem Atom observe)
    (partnerSystem_imageFiniteModulo Atom observe) left right

/-! ## Partner bisimilarity refines reduction bisimilarity -/

/-- The inert partner recovers the plain step, so partner-bisimilar processes
are reduction-bisimilar under the same observations. -/
theorem rhoSystem_bisimilar_of_partner_bisimilar (Atom : Type)
    (observe : Atom → EquationPredicate rhoLanguageDefGSLT) {left right : RhoProcess}
    (bisimilar : (partnerSystem Atom observe).Bisimilar left right) :
    (rhoSystem Atom observe).Bisimilar left right := by
  refine ⟨(partnerSystem Atom observe).Bisimilar, ⟨?_, ?_, ?_⟩, bisimilar⟩
  · intro first second related _ target step
    obtain ⟨target', step', targetEquivalent⟩ := rhoLanguageDefGSLT.rewrites_resp_left
      (rhoLanguageDefGSLT.equations.iseqv.symm (par_nil_equiv first)) step
    obtain ⟨relation, ⟨forward, _, _⟩, relatedPair⟩ := related
    obtain ⟨matched, matchedStep, relatedTargets⟩ :=
      forward relatedPair closedNil step'
    obtain ⟨matched', matchedStep', matchedEquivalent⟩ :=
      rhoLanguageDefGSLT.rewrites_resp_left (par_nil_equiv second) matchedStep
    refine ⟨matched', matchedStep', ?_⟩
    exact (partnerSystem Atom observe).bisimilar_trans
      ((partnerSystem Atom observe).bisimilar_of_equiv targetEquivalent)
      ((partnerSystem Atom observe).bisimilar_trans
        ⟨relation, ⟨forward, ‹_›, ‹_›⟩, relatedTargets⟩
        ((partnerSystem Atom observe).bisimilar_of_equiv matchedEquivalent))
  · intro first second related _ target step
    obtain ⟨target', step', targetEquivalent⟩ := rhoLanguageDefGSLT.rewrites_resp_left
      (rhoLanguageDefGSLT.equations.iseqv.symm (par_nil_equiv second)) step
    obtain ⟨relation, ⟨_, backward, _⟩, relatedPair⟩ := related
    obtain ⟨matched, matchedStep, relatedTargets⟩ :=
      backward relatedPair closedNil step'
    obtain ⟨matched', matchedStep', matchedEquivalent⟩ :=
      rhoLanguageDefGSLT.rewrites_resp_left (par_nil_equiv first) matchedStep
    refine ⟨matched', matchedStep', ?_⟩
    exact (partnerSystem Atom observe).bisimilar_trans
      ((partnerSystem Atom observe).bisimilar_of_equiv
        (rhoLanguageDefGSLT.equations.iseqv.symm matchedEquivalent))
      ((partnerSystem Atom observe).bisimilar_trans
        ⟨relation, ⟨‹_›, backward, ‹_›⟩, relatedTargets⟩
        ((partnerSystem Atom observe).bisimilar_of_equiv
          (rhoLanguageDefGSLT.equations.iseqv.symm targetEquivalent)))
  · intro first second related atom
    obtain ⟨relation, ⟨_, _, atoms⟩, relatedPair⟩ := related
    exact atoms relatedPair atom

/-! ## Canary: reduction bisimilarity is not partner-adequate -/

/-- A receiver waiting on the quoted inert channel. -/
def waitingInput : RhoProcess :=
  ⟨.apply "PInput" [closedNilName.1, .lambda none (.apply "PZero" [])],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.input (.quote .unit) .unit, by decide⟩⟩

/-- The output partner that wakes the receiver. -/
def outputPartner : RhoProcess :=
  ⟨.apply "POutput" [closedNilName.1, .apply "PZero" []],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.output (.quote .unit) .unit, by decide⟩⟩

theorem par_waitingInput_outputPartner : par waitingInput outputPartner = closedCommSource :=
  Subtype.ext rfl

/-- The canonical stepper enumerates no successor: the waiting receiver alone
cannot step. -/
theorem waitingInput_successors :
    rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1 (canonicalize waitingInput.1) = [] := by
  decide +kernel

theorem closedNil_successors :
    rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1 (canonicalize closedNil.1) = [] := by
  decide +kernel

/-- The inert process with the output partner has nothing to receive. -/
theorem nilPartner_successors :
    rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1
      (canonicalize (par closedNil outputPartner).1) = [] := by
  decide +kernel

/-- An empty canonical successor list means no saturated step at all. -/
theorem no_step_of_successors_nil {source : RhoProcess}
    (none : rewriteAt rhoRuleInterpretation rhoBasePremises rhoCalc 1
      (canonicalize source.1) = [])
    (target : RhoProcess) : ¬ rhoLanguageDefGSLT.Step source target := by
  intro step
  obtain ⟨_, member, _⟩ := canonicalSuccessorList_complete source step
  have raw := pattern_mem_of_mem_canonicalSuccessorList member
  rw [none] at raw
  simp at raw

/-- Without a partner, the waiting receiver and the inert process are
bisimilar: neither steps. -/
theorem waitingInput_reduction_bisimilar_nil :
    (rhoSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar waitingInput closedNil := by
  refine ⟨fun first second => first = waitingInput ∧ second = closedNil, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩ _ target step
    exact (no_step_of_successors_nil waitingInput_successors target step).elim
  · rintro _ _ ⟨rfl, rfl⟩ _ target step
    exact (no_step_of_successors_nil closedNil_successors target step).elim
  · rintro _ _ _ atom
    exact atom.elim

/-- The output partner wakes the receiver. -/
theorem partner_step :
    (partnerSystem PEmpty.{1} (fun atom => atom.elim)).act outputPartner waitingInput
      closedCommTarget := by
  show rhoLanguageDefGSLT.Step (par waitingInput outputPartner) closedCommTarget
  rw [par_waitingInput_outputPartner]
  exact closedCommSource_step

/-- One partner diamond separates the two processes. -/
theorem partnerDiamond_separates :
    (partnerSystem PEmpty.{1} (fun atom => atom.elim)).sat (.dia outputPartner .top)
        waitingInput ∧
      ¬ (partnerSystem PEmpty.{1} (fun atom => atom.elim)).sat (.dia outputPartner .top)
        closedNil := by
  constructor
  · exact ⟨closedCommTarget, partner_step, trivial⟩
  · rintro ⟨target, step, _⟩
    exact no_step_of_successors_nil nilPartner_successors target step

/-- Hence the two are not partner-bisimilar. -/
theorem waitingInput_not_partner_bisimilar_nil :
    ¬ (partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar waitingInput closedNil := by
  intro bisimilar
  have same := (partnerSystem PEmpty.{1} (fun atom => atom.elim)).logicallyEquivalent_of_bisimilar
    bisimilar (.dia outputPartner .top)
  exact partnerDiamond_separates.2 (same.mp partnerDiamond_separates.1)

/-- Reduction bisimilarity is strictly coarser than partner bisimilarity on
rho, so the partner labels are necessary for a congruence-adequate logic. -/
theorem reduction_bisimilarity_not_partner_adequate :
    (rhoSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar waitingInput closedNil ∧
      ¬ (partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar waitingInput closedNil :=
  ⟨waitingInput_reduction_bisimilar_nil, waitingInput_not_partner_bisimilar_nil⟩

/-! ## The box-free OSLF fragment on both rho presentations -/

/-- Box-free OSLF equivalence over the established rho GSLT is forward
bisimilarity, unconditionally. -/
theorem forwardEquivalent_iff_bisimilar (I : String → EquationPredicate rhoLanguageDefGSLT)
    (left right : RhoProcess) :
    ForwardEquivalent rhoLanguageDefGSLT I left right ↔
      (forwardSystem rhoLanguageDefGSLT I).Bisimilar left right :=
  forwardEquivalent_iff_bisimilar_of_enumeration rhoSuccessorClassEnumeration I left right

/-- The same over the public interpreted rho presentation, the exact GSLT of
the public rho OSLF. -/
theorem presentedForwardEquivalent_iff_bisimilar
    (I : String → EquationPredicate rhoReflectiveGSLT) (left right : rhoReflectiveGSLT.Term) :
    ForwardEquivalent rhoReflectiveGSLT I left right ↔
      (forwardSystem rhoReflectiveGSLT I).Bisimilar left right :=
  forwardEquivalent_iff_bisimilar_of_enumeration presentedRhoSuccessorClassEnumeration I
    left right

#print axioms partnerLogicallyEquivalent_iff_bisimilar
#print axioms partnerFormulaNativeTypes_equivalent_iff_bisimilar
#print axioms rhoSystem_bisimilar_of_partner_bisimilar
#print axioms reduction_bisimilarity_not_partner_adequate
#print axioms presentedForwardEquivalent_iff_bisimilar

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy
