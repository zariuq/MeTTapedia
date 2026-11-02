import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedEnvironmentInterpretation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeGuardedApplicationSpineControls

/-!
# Open typed programs interpreted in a closed target environment

The source has a type variable and a value in that type; the target has no
variables. Predicate-guard realization supplies the actual closed inputs.
A second control opens an existential value, applies the typed identity and
closes a result containing its computation equation. An empty guard refuses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.GuardedEnvironmentInterpretationControls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading HOL.PredicateContexts
open NativeGuardedRealizability.Controls
open NativeGuardedApplicationSpineControls (completed completed_free)

def target : List (HOL.Formula Const []) := assumptions roots []
def fullNumber : HOL.ClosedTerm Const (.arr number .prop) := .lam .top

def rootsEvidence : HOL.ProofSyntax.HypothesisSubstitution (assumptions roots []) target :=
  HOL.ProofSyntax.HypothesisSubstitution.identity _

def emptyGuards : (Telescope.nil : Telescope Const []).Realizes emptyAssignment target :=
  fun impossible => nomatch impossible

def fullPredicateProof : HOL.ProofSyntax Const target
    (.app (HOL.PredicateProducts.full predicateType) fullNumber) :=
  .impE (.eqPropER (.beta fullNumber .top)) .topI

def baseImages : HOL.Subst Const [predicateType] [] := HOL.Subst.cons fullNumber emptyAssignment
def baseGuards : baseContext.telescope.Realizes baseImages target :=
  Telescope.Realizes.cons emptyGuards (HOL.PredicateProducts.full predicateType) fullNumber fullPredicateProof

def valueProof : HOL.ProofSyntax Const target (.app fullNumber raw.zero) :=
  .impE (.eqPropER (.beta raw.zero .top)) .topI

def images : HOL.Subst Const [number, predicateType] [] := HOL.Subst.cons raw.zero baseImages
def guards : valueContext.telescope.Realizes images target :=
  Telescope.Realizes.cons baseGuards predicate raw.zero valueProof

theorem roots_free : ∀ occurrence, (rootsEvidence occurrence).FunctionExtensionalityFree := by
  intro occurrence
  trivial

theorem base_guards_free : ∀ {type} (index : HOL.Var [predicateType] type),
    (baseGuards index).FunctionExtensionalityFree := by
  apply Telescope.Realizes.cons_free
  · intro type impossible
    nomatch impossible
  · exact ⟨True.intro, True.intro⟩

theorem guards_free : ∀ {type} (index : HOL.Var [number, predicateType] type),
    (guards index).FunctionExtensionalityFree :=
  Telescope.Realizes.cons_free baseGuards predicate raw.zero valueProof base_guards_free ⟨True.intro, True.intro⟩

def realized := completed.realize images guards rootsEvidence

theorem realized_free : realized.FunctionExtensionalityFree :=
  completed.realize_free images guards rootsEvidence guards_free roots_free completed_free

theorem two_source_guards : valueContext.telescope.hypotheses.length = 2 := rfl

theorem interpreted_result : model.denote (HOL.subst images completed.term) emptyValues = ULift.up 0 := rfl

def sourceGoal : HOL.Formula Const [predicateType] :=
  .ex (.and (.app (.var (.vs .vz)) (.var .vz))
    (.eq (.app (.lam (.var .vz)) (.var .vz)) (.var .vz)))

def continuation : HOL.ProofSyntax Const (valueContext.hypotheses roots) (HOL.weaken sourceGoal) := by
  classical
  apply HOL.ProofSyntax.exI appliedIdentity.term
  change HOL.ProofSyntax Const (valueContext.hypotheses roots)
    (.and (.app (HOL.weaken predicate) appliedIdentity.term)
      (.eq (.app (.lam (.var .vz)) appliedIdentity.term) appliedIdentity.term))
  have same : appliedIdentity.predicate = HOL.weaken predicate :=
    Reader.term_unique appliedIdentity.typeRead
      (Reads.var (lex := lex) (.vs .vz : HOL.Var [number, predicateType] predicateType))
  exact .andI
    (HOL.ProofSyntax.castIndices rfl (congrArg (fun code => HOL.Term.app code appliedIdentity.term) same) appliedIdentity.member)
    (.beta appliedIdentity.term (.var .vz))

theorem continuation_free : continuation.FunctionExtensionalityFree := by
  unfold continuation
  exact ⟨(HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr application_free, True.intro⟩

def existsInput : HOL.ProofSyntax Const target (.ex (.app (HOL.weaken fullNumber) (.var .vz))) :=
  .exI raw.zero valueProof

def opened := baseContext.eliminateWitness baseImages baseGuards rootsEvidence predicate domain_read domain_formed
  existsInput continuation

theorem opened_free : opened.FunctionExtensionalityFree :=
  baseContext.eliminateWitness_free baseImages baseGuards rootsEvidence predicate domain_read domain_formed
    existsInput continuation base_guards_free roots_free ⟨True.intro, True.intro⟩ continuation_free

theorem opened_valid : (model.denote (HOL.subst baseImages sourceGoal) emptyValues).down :=
  HOL.Soundness.extDerivation_sound opened.erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun impossible => nomatch impossible) (by
      simpa only [target, GuardedContext.hypotheses, emptyContext, Telescope.hypotheses, List.append_nil]
        using empty_background_holds)

theorem empty_guard_refused : ¬ Nonempty (valueContext.telescope.Realizes wrongCode target) := by
  rintro ⟨bad⟩
  have impossible := HOL.Soundness.extDerivation_sound
    (bad (.vz : HOL.Var [number, predicateType] number)).erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun impossible => nomatch impossible) (by
      simpa only [target, GuardedContext.hypotheses, emptyContext, Telescope.hypotheses, List.append_nil]
        using empty_background_holds)
  exact impossible

#print axioms realized_free
#print axioms opened_free
#print axioms opened_valid
#print axioms empty_guard_refused

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.GuardedEnvironmentInterpretationControls
